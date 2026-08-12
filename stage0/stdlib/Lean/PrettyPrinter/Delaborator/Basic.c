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
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "builtin_delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 78, 157, 22, 7, 109, 94, 150)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 48, 28, 192, 106, 44, 69, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Register a delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 145, 52, 44, 66, 160, 163, 69)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "delabAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 105, 4, 51, 2, 59, 203, 237)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 513, .m_capacity = 513, .m_length = 512, .m_data = "Registers a delaborator.\n\n`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the\n`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`, elaborators\nfor `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\") to reduce\nspecial casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first.\n"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(102) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(127) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__6_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7_value;
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(231, 152, 1, 212, 81, 225, 23, 202)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "appUnexpanderAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 177, 70, 181, 38, 19, 76, 236)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 620, .m_capacity = 620, .m_length = 619, .m_data = "Registers an unexpander for applications of a given constant.\n\n`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant\n`c`. The unexpander is passed the result of pre-pretty printing the application *without*\nimplicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,\nit will not be called at all.\n\nUnexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without\nspecial imports. This however also makes them much less capable since they can only transform\nsyntax and don't have access to the expression tree.\n"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(469) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(491) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(482) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(482) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 19, 214, 208, 28, 243, 5, 52)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 164, 190, 165, 103, 227, 105, 51)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 183, 224, 255, 20, 2, 99, 61)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 0, 36, 13, 230, 137, 208, 68)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 99, 145, 72, 150, 13, 224, 205)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 207, 248, 169, 211, 175, 254, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 170, 24, 58, 43, 56, 104, 232)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 123, 18, 109, 183, 228, 66, 1)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 193, 243, 64, 48, 31, 65, 146)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 168, 97, 241, 156, 42, 72, 1)}};
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
v___x_296_ = lean_st_ref_set(v___y_282_, v___x_295_);
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
v___x_332_ = lean_st_ref_set(v___y_314_, v___x_331_);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_builtin_354_, lean_object* v_declName_355_, lean_object* v_key_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_builtin_362_, lean_object* v_declName_363_, lean_object* v_key_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v_builtin_boxed_368_; lean_object* v_res_369_; 
v_builtin_boxed_368_ = lean_unbox(v_builtin_362_);
v_res_369_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_builtin_boxed_368_, v_declName_363_, v_key_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v_key_364_);
lean_dec(v_declName_363_);
return v_res_369_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_375_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_379_ = ((size_t)5ULL);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_unsigned_to_nat(32u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
v___x_383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_384_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set(v___x_384_, 3, v___x_380_);
lean_ctor_set_usize(v___x_384_, 4, v___x_379_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_box(1);
v___x_386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_410_, lean_object* v_declHint_411_, lean_object* v___y_412_){
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
v___x_422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
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
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_c_427_);
v___x_431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
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
v___x_445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_c_427_);
v___x_447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_MessageData_ofName(v_mod_443_);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
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
v___x_458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_c_427_);
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_MessageData_ofName(v_mod_443_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_473_, lean_object* v_declHint_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_473_, v_declHint_474_, v___y_475_);
lean_dec(v___y_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(lean_object* v_msg_478_, lean_object* v_declHint_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_493_; 
v___x_483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_478_, v_declHint_479_, v___y_481_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_494_, lean_object* v_declHint_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(v_msg_494_, v_declHint_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v_env_505_; lean_object* v_options_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_env_505_);
lean_dec(v___x_504_);
v_options_506_ = lean_ctor_get(v___y_501_, 2);
v___x_507_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_508_ = lean_unsigned_to_nat(32u);
v___x_509_ = lean_mk_empty_array_with_capacity(v___x_508_);
lean_dec_ref(v___x_509_);
v___x_510_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
lean_inc_ref(v_options_506_);
v___x_511_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_511_, 0, v_env_505_);
lean_ctor_set(v___x_511_, 1, v___x_507_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
lean_ctor_set(v___x_511_, 3, v_options_506_);
v___x_512_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_msgData_500_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msgData_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_ref_523_; lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_ref_523_ = lean_ctor_get(v___y_520_, 5);
v___x_524_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msg_519_, v___y_520_, v___y_521_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_ref_523_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_ref_523_);
lean_ctor_set(v___x_529_, 1, v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 1);
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg___boxed(lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_fileName_544_; lean_object* v_fileMap_545_; lean_object* v_options_546_; lean_object* v_currRecDepth_547_; lean_object* v_maxRecDepth_548_; lean_object* v_ref_549_; lean_object* v_currNamespace_550_; lean_object* v_openDecls_551_; lean_object* v_initHeartbeats_552_; lean_object* v_maxHeartbeats_553_; lean_object* v_quotContext_554_; lean_object* v_currMacroScope_555_; uint8_t v_diag_556_; lean_object* v_cancelTk_x3f_557_; uint8_t v_suppressElabErrors_558_; lean_object* v_inheritedTraceOptions_559_; lean_object* v_ref_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_fileName_544_ = lean_ctor_get(v___y_541_, 0);
v_fileMap_545_ = lean_ctor_get(v___y_541_, 1);
v_options_546_ = lean_ctor_get(v___y_541_, 2);
v_currRecDepth_547_ = lean_ctor_get(v___y_541_, 3);
v_maxRecDepth_548_ = lean_ctor_get(v___y_541_, 4);
v_ref_549_ = lean_ctor_get(v___y_541_, 5);
v_currNamespace_550_ = lean_ctor_get(v___y_541_, 6);
v_openDecls_551_ = lean_ctor_get(v___y_541_, 7);
v_initHeartbeats_552_ = lean_ctor_get(v___y_541_, 8);
v_maxHeartbeats_553_ = lean_ctor_get(v___y_541_, 9);
v_quotContext_554_ = lean_ctor_get(v___y_541_, 10);
v_currMacroScope_555_ = lean_ctor_get(v___y_541_, 11);
v_diag_556_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*14);
v_cancelTk_x3f_557_ = lean_ctor_get(v___y_541_, 12);
v_suppressElabErrors_558_ = lean_ctor_get_uint8(v___y_541_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_559_ = lean_ctor_get(v___y_541_, 13);
v_ref_560_ = l_Lean_replaceRef(v_ref_539_, v_ref_549_);
lean_inc_ref(v_inheritedTraceOptions_559_);
lean_inc(v_cancelTk_x3f_557_);
lean_inc(v_currMacroScope_555_);
lean_inc(v_quotContext_554_);
lean_inc(v_maxHeartbeats_553_);
lean_inc(v_initHeartbeats_552_);
lean_inc(v_openDecls_551_);
lean_inc(v_currNamespace_550_);
lean_inc(v_maxRecDepth_548_);
lean_inc(v_currRecDepth_547_);
lean_inc_ref(v_options_546_);
lean_inc_ref(v_fileMap_545_);
lean_inc_ref(v_fileName_544_);
v___x_561_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_561_, 0, v_fileName_544_);
lean_ctor_set(v___x_561_, 1, v_fileMap_545_);
lean_ctor_set(v___x_561_, 2, v_options_546_);
lean_ctor_set(v___x_561_, 3, v_currRecDepth_547_);
lean_ctor_set(v___x_561_, 4, v_maxRecDepth_548_);
lean_ctor_set(v___x_561_, 5, v_ref_560_);
lean_ctor_set(v___x_561_, 6, v_currNamespace_550_);
lean_ctor_set(v___x_561_, 7, v_openDecls_551_);
lean_ctor_set(v___x_561_, 8, v_initHeartbeats_552_);
lean_ctor_set(v___x_561_, 9, v_maxHeartbeats_553_);
lean_ctor_set(v___x_561_, 10, v_quotContext_554_);
lean_ctor_set(v___x_561_, 11, v_currMacroScope_555_);
lean_ctor_set(v___x_561_, 12, v_cancelTk_x3f_557_);
lean_ctor_set(v___x_561_, 13, v_inheritedTraceOptions_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*14, v_diag_556_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*14 + 1, v_suppressElabErrors_558_);
v___x_562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_540_, v___x_561_, v___y_542_);
lean_dec_ref_known(v___x_561_, 14);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_563_, v_msg_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v_ref_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(lean_object* v_ref_569_, lean_object* v_msg_570_, lean_object* v_declHint_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(v_msg_570_, v_declHint_571_, v___y_572_, v___y_573_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_569_, v_a_576_, v___y_572_, v___y_573_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_ref_578_, lean_object* v_msg_579_, lean_object* v_declHint_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_578_, v_msg_579_, v_declHint_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v_ref_578_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__0));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(lean_object* v_ref_591_, lean_object* v_constName_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_596_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1);
v___x_597_ = 0;
lean_inc(v_constName_592_);
v___x_598_ = l_Lean_MessageData_ofConstName(v_constName_592_, v___x_597_);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_591_, v___x_601_, v_constName_592_, v___y_593_, v___y_594_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___boxed(lean_object* v_ref_603_, lean_object* v_constName_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_603_, v_constName_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_ref_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(lean_object* v_constName_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_ref_613_; lean_object* v___x_614_; 
v_ref_613_ = lean_ctor_get(v___y_610_, 5);
v___x_614_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_613_, v_constName_609_, v___y_610_, v___y_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_constName_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_constName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; lean_object* v_env_625_; uint8_t v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_st_ref_get(v___y_622_);
v_env_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_ref(v_env_625_);
lean_dec(v___x_624_);
v___x_626_ = 0;
lean_inc(v_constName_620_);
v___x_627_ = l_Lean_Environment_findConstVal_x3f(v_env_625_, v_constName_620_, v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_620_, v___y_621_, v___y_622_);
return v___x_628_;
}
else
{
lean_object* v_val_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_constName_620_);
v_val_629_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_val_629_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 0);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_629_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_constName_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_constName_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = l_List_reverse___redArg(v_a_643_);
return v___x_644_;
}
else
{
lean_object* v_head_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v_head_645_ = lean_ctor_get(v_a_642_, 0);
v_tail_646_ = lean_ctor_get(v_a_642_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_655_ == 0)
{
v___x_648_ = v_a_642_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_head_645_);
lean_dec(v_a_642_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_mkLevelParam(v_head_645_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_a_643_);
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_643_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_a_642_ = v_tail_646_;
v_a_643_ = v___x_652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_constName_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
lean_inc(v_constName_656_);
v___x_660_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_constName_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_672_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_levelParams_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_levelParams_665_ = lean_ctor_get(v_a_661_, 1);
lean_inc(v_levelParams_665_);
lean_dec(v_a_661_);
v___x_666_ = lean_box(0);
v___x_667_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_levelParams_665_, v___x_666_);
v___x_668_ = l_Lean_mkConst(v_constName_656_, v___x_667_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_668_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_constName_656_);
v_a_673_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_660_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_660_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_constName_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_constName_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(lean_object* v_t_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_infoState_690_; uint8_t v_enabled_691_; 
v___x_689_ = lean_st_ref_get(v___y_687_);
v_infoState_690_ = lean_ctor_get(v___x_689_, 7);
lean_inc_ref(v_infoState_690_);
lean_dec(v___x_689_);
v_enabled_691_ = lean_ctor_get_uint8(v_infoState_690_, sizeof(void*)*3);
lean_dec_ref(v_infoState_690_);
if (v_enabled_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_t_686_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v_infoState_695_; lean_object* v_env_696_; lean_object* v_nextMacroScope_697_; lean_object* v_ngen_698_; lean_object* v_auxDeclNGen_699_; lean_object* v_traceState_700_; lean_object* v_cache_701_; lean_object* v_messages_702_; lean_object* v_snapshotTasks_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_725_; 
v___x_694_ = lean_st_ref_take(v___y_687_);
v_infoState_695_ = lean_ctor_get(v___x_694_, 7);
v_env_696_ = lean_ctor_get(v___x_694_, 0);
v_nextMacroScope_697_ = lean_ctor_get(v___x_694_, 1);
v_ngen_698_ = lean_ctor_get(v___x_694_, 2);
v_auxDeclNGen_699_ = lean_ctor_get(v___x_694_, 3);
v_traceState_700_ = lean_ctor_get(v___x_694_, 4);
v_cache_701_ = lean_ctor_get(v___x_694_, 5);
v_messages_702_ = lean_ctor_get(v___x_694_, 6);
v_snapshotTasks_703_ = lean_ctor_get(v___x_694_, 8);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_725_ == 0)
{
v___x_705_ = v___x_694_;
v_isShared_706_ = v_isSharedCheck_725_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snapshotTasks_703_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_702_);
lean_inc(v_cache_701_);
lean_inc(v_traceState_700_);
lean_inc(v_auxDeclNGen_699_);
lean_inc(v_ngen_698_);
lean_inc(v_nextMacroScope_697_);
lean_inc(v_env_696_);
lean_dec(v___x_694_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_725_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v_enabled_707_; lean_object* v_assignment_708_; lean_object* v_lazyAssignment_709_; lean_object* v_trees_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_724_; 
v_enabled_707_ = lean_ctor_get_uint8(v_infoState_695_, sizeof(void*)*3);
v_assignment_708_ = lean_ctor_get(v_infoState_695_, 0);
v_lazyAssignment_709_ = lean_ctor_get(v_infoState_695_, 1);
v_trees_710_ = lean_ctor_get(v_infoState_695_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_infoState_695_);
if (v_isSharedCheck_724_ == 0)
{
v___x_712_ = v_infoState_695_;
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_trees_710_);
lean_inc(v_lazyAssignment_709_);
lean_inc(v_assignment_708_);
lean_dec(v_infoState_695_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_trees_710_, v_t_686_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 2, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_assignment_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_lazyAssignment_709_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v___x_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_723_, sizeof(void*)*3, v_enabled_707_);
v___x_716_ = v_reuseFailAlloc_723_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 7, v___x_716_);
v___x_718_ = v___x_705_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_env_696_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_nextMacroScope_697_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_ngen_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_auxDeclNGen_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_traceState_700_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_cache_701_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_messages_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v_snapshotTasks_703_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_set(v___y_687_, v___x_718_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v_t_726_, v___y_727_);
lean_dec(v___y_727_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_unsigned_to_nat(32u);
v___x_731_ = lean_mk_empty_array_with_capacity(v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_733_ = ((size_t)5ULL);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_unsigned_to_nat(32u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
v___x_737_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0);
v___x_738_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v___x_734_);
lean_ctor_set(v___x_738_, 3, v___x_734_);
lean_ctor_set_usize(v___x_738_, 4, v___x_733_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_t_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_infoState_744_; uint8_t v_enabled_745_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_infoState_744_ = lean_ctor_get(v___x_743_, 7);
lean_inc_ref(v_infoState_744_);
lean_dec(v___x_743_);
v_enabled_745_ = lean_ctor_get_uint8(v_infoState_744_, sizeof(void*)*3);
lean_dec_ref(v_infoState_744_);
if (v_enabled_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_t_739_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v_t_739_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v___x_749_, v___y_741_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_t_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v_t_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(lean_object* v_stx_756_, lean_object* v_n_757_, lean_object* v_expectedType_x3f_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_n_757_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = lean_box(0);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_stx_756_);
v___x_766_ = l_Lean_LocalContext_empty;
v___x_767_ = 0;
v___x_768_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
lean_ctor_set(v___x_768_, 2, v_expectedType_x3f_758_);
lean_ctor_set(v___x_768_, 3, v_a_763_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*4, v___x_767_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*4 + 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___x_770_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v___x_769_, v___y_759_, v___y_760_);
return v___x_770_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_expectedType_x3f_758_);
lean_dec(v_stx_756_);
v_a_771_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_762_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_779_, lean_object* v_n_780_, lean_object* v_expectedType_x3f_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_stx_779_, v_n_780_, v_expectedType_x3f_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_box(0);
return v___x_788_;
}
else
{
lean_object* v_key_789_; lean_object* v_value_790_; lean_object* v_tail_791_; uint8_t v___x_792_; 
v_key_789_ = lean_ctor_get(v_x_787_, 0);
v_value_790_ = lean_ctor_get(v_x_787_, 1);
v_tail_791_ = lean_ctor_get(v_x_787_, 2);
v___x_792_ = lean_name_eq(v_key_789_, v_a_786_);
if (v___x_792_ == 0)
{
v_x_787_ = v_tail_791_;
goto _start;
}
else
{
lean_object* v___x_794_; 
lean_inc(v_value_790_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_value_790_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_795_, v_x_796_);
lean_dec(v_x_796_);
lean_dec(v_a_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_m_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_buckets_800_; lean_object* v___x_801_; uint64_t v___y_803_; 
v_buckets_800_ = lean_ctor_get(v_m_798_, 1);
v___x_801_ = lean_array_get_size(v_buckets_800_);
if (lean_obj_tag(v_a_799_) == 0)
{
uint64_t v___x_817_; 
v___x_817_ = 1723ULL;
v___y_803_ = v___x_817_;
goto v___jp_802_;
}
else
{
uint64_t v_hash_818_; 
v_hash_818_ = lean_ctor_get_uint64(v_a_799_, sizeof(void*)*2);
v___y_803_ = v_hash_818_;
goto v___jp_802_;
}
v___jp_802_:
{
uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v_fold_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_804_ = 32ULL;
v___x_805_ = lean_uint64_shift_right(v___y_803_, v___x_804_);
v_fold_806_ = lean_uint64_xor(v___y_803_, v___x_805_);
v___x_807_ = 16ULL;
v___x_808_ = lean_uint64_shift_right(v_fold_806_, v___x_807_);
v___x_809_ = lean_uint64_xor(v_fold_806_, v___x_808_);
v___x_810_ = lean_uint64_to_usize(v___x_809_);
v___x_811_ = lean_usize_of_nat(v___x_801_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_sub(v___x_811_, v___x_812_);
v___x_814_ = lean_usize_land(v___x_810_, v___x_813_);
v___x_815_ = lean_array_uget_borrowed(v_buckets_800_, v___x_814_);
v___x_816_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_799_, v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_m_819_);
return v_res_821_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_822_; double v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_float_of_nat(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_cls_827_, lean_object* v_msg_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_ref_832_; lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_878_; 
v_ref_832_ = lean_ctor_get(v___y_829_, 5);
v___x_833_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msg_828_, v___y_829_, v___y_830_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_878_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_878_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_878_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_traceState_839_; lean_object* v_env_840_; lean_object* v_nextMacroScope_841_; lean_object* v_ngen_842_; lean_object* v_auxDeclNGen_843_; lean_object* v_cache_844_; lean_object* v_messages_845_; lean_object* v_infoState_846_; lean_object* v_snapshotTasks_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_877_; 
v___x_838_ = lean_st_ref_take(v___y_830_);
v_traceState_839_ = lean_ctor_get(v___x_838_, 4);
v_env_840_ = lean_ctor_get(v___x_838_, 0);
v_nextMacroScope_841_ = lean_ctor_get(v___x_838_, 1);
v_ngen_842_ = lean_ctor_get(v___x_838_, 2);
v_auxDeclNGen_843_ = lean_ctor_get(v___x_838_, 3);
v_cache_844_ = lean_ctor_get(v___x_838_, 5);
v_messages_845_ = lean_ctor_get(v___x_838_, 6);
v_infoState_846_ = lean_ctor_get(v___x_838_, 7);
v_snapshotTasks_847_ = lean_ctor_get(v___x_838_, 8);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_877_ == 0)
{
v___x_849_ = v___x_838_;
v_isShared_850_ = v_isSharedCheck_877_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snapshotTasks_847_);
lean_inc(v_infoState_846_);
lean_inc(v_messages_845_);
lean_inc(v_cache_844_);
lean_inc(v_traceState_839_);
lean_inc(v_auxDeclNGen_843_);
lean_inc(v_ngen_842_);
lean_inc(v_nextMacroScope_841_);
lean_inc(v_env_840_);
lean_dec(v___x_838_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_877_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint64_t v_tid_851_; lean_object* v_traces_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_876_; 
v_tid_851_ = lean_ctor_get_uint64(v_traceState_839_, sizeof(void*)*1);
v_traces_852_ = lean_ctor_get(v_traceState_839_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_traceState_839_);
if (v_isSharedCheck_876_ == 0)
{
v___x_854_ = v_traceState_839_;
v_isShared_855_ = v_isSharedCheck_876_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_traces_852_);
lean_dec(v_traceState_839_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_876_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; double v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0);
v___x_858_ = 0;
v___x_859_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_860_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_860_, 0, v_cls_827_);
lean_ctor_set(v___x_860_, 1, v___x_856_);
lean_ctor_set(v___x_860_, 2, v___x_859_);
lean_ctor_set_float(v___x_860_, sizeof(void*)*3, v___x_857_);
lean_ctor_set_float(v___x_860_, sizeof(void*)*3 + 8, v___x_857_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*3 + 16, v___x_858_);
v___x_861_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2));
v___x_862_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v_a_834_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_inc(v_ref_832_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_ref_832_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_PersistentArray_push___redArg(v_traces_852_, v___x_863_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_864_);
v___x_866_ = v___x_854_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_864_);
lean_ctor_set_uint64(v_reuseFailAlloc_875_, sizeof(void*)*1, v_tid_851_);
v___x_866_ = v_reuseFailAlloc_875_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v___x_866_);
v___x_868_ = v___x_849_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_env_840_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_nextMacroScope_841_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_ngen_842_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_auxDeclNGen_843_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_874_, 5, v_cache_844_);
lean_ctor_set(v_reuseFailAlloc_874_, 6, v_messages_845_);
lean_ctor_set(v_reuseFailAlloc_874_, 7, v_infoState_846_);
lean_ctor_set(v_reuseFailAlloc_874_, 8, v_snapshotTasks_847_);
v___x_868_ = v_reuseFailAlloc_874_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_st_ref_set(v___y_830_, v___x_868_);
v___x_870_ = lean_box(0);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_870_);
v___x_872_ = v___x_836_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_cls_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_cls_879_, v_msg_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_884_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_885_, lean_object* v_i_886_, lean_object* v_k_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_array_get_size(v_keys_885_);
v___x_889_ = lean_nat_dec_lt(v_i_886_, v___x_888_);
if (v___x_889_ == 0)
{
lean_dec(v_i_886_);
return v___x_889_;
}
else
{
lean_object* v_k_x27_890_; uint8_t v___x_891_; 
v_k_x27_890_ = lean_array_fget_borrowed(v_keys_885_, v_i_886_);
v___x_891_ = l_Lean_instBEqExtraModUse_beq(v_k_887_, v_k_x27_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_nat_add(v_i_886_, v___x_892_);
lean_dec(v_i_886_);
v_i_886_ = v___x_893_;
goto _start;
}
else
{
lean_dec(v_i_886_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_895_, lean_object* v_i_896_, lean_object* v_k_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_895_, v_i_896_, v_k_897_);
lean_dec_ref(v_k_897_);
lean_dec_ref(v_keys_895_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_900_, size_t v_x_901_, lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
lean_object* v_es_903_; lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v_j_907_; lean_object* v___x_908_; 
v_es_903_ = lean_ctor_get(v_x_900_, 0);
v___x_904_ = lean_box(2);
v___x_905_ = ((size_t)31ULL);
v___x_906_ = lean_usize_land(v_x_901_, v___x_905_);
v_j_907_ = lean_usize_to_nat(v___x_906_);
v___x_908_ = lean_array_get_borrowed(v___x_904_, v_es_903_, v_j_907_);
lean_dec(v_j_907_);
switch(lean_obj_tag(v___x_908_))
{
case 0:
{
lean_object* v_key_909_; uint8_t v___x_910_; 
v_key_909_ = lean_ctor_get(v___x_908_, 0);
v___x_910_ = l_Lean_instBEqExtraModUse_beq(v_x_902_, v_key_909_);
return v___x_910_;
}
case 1:
{
lean_object* v_node_911_; size_t v___x_912_; size_t v___x_913_; 
v_node_911_ = lean_ctor_get(v___x_908_, 0);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_usize_shift_right(v_x_901_, v___x_912_);
v_x_900_ = v_node_911_;
v_x_901_ = v___x_913_;
goto _start;
}
default: 
{
uint8_t v___x_915_; 
v___x_915_ = 0;
return v___x_915_;
}
}
}
else
{
lean_object* v_ks_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_ks_916_ = lean_ctor_get(v_x_900_, 0);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_916_, v___x_917_, v_x_902_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
size_t v_x_7978__boxed_922_; uint8_t v_res_923_; lean_object* v_r_924_; 
v_x_7978__boxed_922_ = lean_unbox_usize(v_x_920_);
lean_dec(v_x_920_);
v_res_923_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_919_, v_x_7978__boxed_922_, v_x_921_);
lean_dec_ref(v_x_921_);
lean_dec_ref(v_x_919_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
uint64_t v___x_927_; size_t v___x_928_; uint8_t v___x_929_; 
v___x_927_ = l_Lean_instHashableExtraModUse_hash(v_x_926_);
v___x_928_ = lean_uint64_to_usize(v___x_927_);
v___x_929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_925_, v___x_928_, v_x_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_930_, v_x_931_);
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_937_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_938_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_cls_958_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7));
v___x_959_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_960_ = l_Lean_Name_append(v___x_959_, v_cls_958_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_mod_971_, uint8_t v_isMeta_972_, lean_object* v_hint_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_env_978_; uint8_t v_isExporting_979_; lean_object* v___x_980_; lean_object* v_env_981_; lean_object* v___x_982_; lean_object* v_entry_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___y_988_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_977_ = lean_st_ref_get(v___y_975_);
v_env_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_977_);
v_isExporting_979_ = lean_ctor_get_uint8(v_env_978_, sizeof(void*)*8);
lean_dec_ref(v_env_978_);
v___x_980_ = lean_st_ref_get(v___y_975_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_980_);
v___x_982_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2);
lean_inc(v_mod_971_);
v_entry_983_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_983_, 0, v_mod_971_);
lean_ctor_set_uint8(v_entry_983_, sizeof(void*)*1, v_isExporting_979_);
lean_ctor_set_uint8(v_entry_983_, sizeof(void*)*1 + 1, v_isMeta_972_);
v___x_984_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_985_ = lean_box(1);
v___x_986_ = lean_box(0);
v___x_1013_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_982_, v___x_984_, v_env_981_, v___x_985_, v___x_986_);
v___x_1014_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_1013_, v_entry_983_);
lean_dec(v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v_options_1015_; uint8_t v_hasTrace_1016_; 
v_options_1015_ = lean_ctor_get(v___y_974_, 2);
v_hasTrace_1016_ = lean_ctor_get_uint8(v_options_1015_, sizeof(void*)*1);
if (v_hasTrace_1016_ == 0)
{
lean_dec(v_hint_973_);
lean_dec(v_mod_971_);
v___y_988_ = v___y_975_;
goto v___jp_987_;
}
else
{
lean_object* v_inheritedTraceOptions_1017_; lean_object* v_cls_1018_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_inheritedTraceOptions_1017_ = lean_ctor_get(v___y_974_, 13);
v_cls_1018_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7));
v___x_1038_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15);
v___x_1039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1017_, v_options_1015_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_hint_973_);
lean_dec(v_mod_971_);
v___y_988_ = v___y_975_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1040_; lean_object* v___y_1042_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17);
if (v_isExporting_979_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__22));
v___y_1042_ = v___x_1049_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__23));
v___y_1042_ = v___x_1050_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_inc_ref(v___y_1042_);
v___x_1043_ = l_Lean_stringToMessageData(v___y_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1040_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
if (v_isMeta_972_ == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20));
v___y_1025_ = v___x_1046_;
v___y_1026_ = v___x_1047_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__21));
v___y_1025_ = v___x_1046_;
v___y_1026_ = v___x_1048_;
goto v___jp_1024_;
}
}
}
v___jp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1020_);
lean_ctor_set(v___x_1022_, 1, v___y_1021_);
v___x_1023_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_cls_1018_, v___x_1022_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_988_ = v___y_975_;
goto v___jp_987_;
}
else
{
lean_dec_ref_known(v_entry_983_, 1);
return v___x_1023_;
}
}
v___jp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_inc_ref(v___y_1026_);
v___x_1027_ = l_Lean_stringToMessageData(v___y_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1025_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_MessageData_ofName(v_mod_971_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_Name_isAnonymous(v_hint_973_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11);
v___x_1035_ = l_Lean_MessageData_ofName(v_hint_973_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___y_1020_ = v___x_1032_;
v___y_1021_ = v___x_1036_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_hint_973_);
v___x_1037_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12);
v___y_1020_ = v___x_1032_;
v___y_1021_ = v___x_1037_;
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v_entry_983_, 1);
lean_dec(v_hint_973_);
lean_dec(v_mod_971_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
v___jp_987_:
{
lean_object* v___x_989_; lean_object* v_toEnvExtension_990_; lean_object* v_env_991_; lean_object* v_nextMacroScope_992_; lean_object* v_ngen_993_; lean_object* v_auxDeclNGen_994_; lean_object* v_traceState_995_; lean_object* v_messages_996_; lean_object* v_infoState_997_; lean_object* v_snapshotTasks_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v___x_989_ = lean_st_ref_take(v___y_988_);
v_toEnvExtension_990_ = lean_ctor_get(v___x_984_, 0);
v_env_991_ = lean_ctor_get(v___x_989_, 0);
v_nextMacroScope_992_ = lean_ctor_get(v___x_989_, 1);
v_ngen_993_ = lean_ctor_get(v___x_989_, 2);
v_auxDeclNGen_994_ = lean_ctor_get(v___x_989_, 3);
v_traceState_995_ = lean_ctor_get(v___x_989_, 4);
v_messages_996_ = lean_ctor_get(v___x_989_, 6);
v_infoState_997_ = lean_ctor_get(v___x_989_, 7);
v_snapshotTasks_998_ = lean_ctor_get(v___x_989_, 8);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_989_, 5);
lean_dec(v_unused_1012_);
v___x_1000_ = v___x_989_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snapshotTasks_998_);
lean_inc(v_infoState_997_);
lean_inc(v_messages_996_);
lean_inc(v_traceState_995_);
lean_inc(v_auxDeclNGen_994_);
lean_inc(v_ngen_993_);
lean_inc(v_nextMacroScope_992_);
lean_inc(v_env_991_);
lean_dec(v___x_989_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_asyncMode_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v_asyncMode_1002_ = lean_ctor_get(v_toEnvExtension_990_, 2);
v___x_1003_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_984_, v_env_991_, v_entry_983_, v_asyncMode_1002_, v___x_986_);
v___x_1004_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 5, v___x_1004_);
lean_ctor_set(v___x_1000_, 0, v___x_1003_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_nextMacroScope_992_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_ngen_993_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_auxDeclNGen_994_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_traceState_995_);
lean_ctor_set(v_reuseFailAlloc_1010_, 5, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 6, v_messages_996_);
lean_ctor_set(v_reuseFailAlloc_1010_, 7, v_infoState_997_);
lean_ctor_set(v_reuseFailAlloc_1010_, 8, v_snapshotTasks_998_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_st_ref_set(v___y_988_, v___x_1006_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_mod_1053_, lean_object* v_isMeta_1054_, lean_object* v_hint_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_isMeta_boxed_1059_; lean_object* v_res_1060_; 
v_isMeta_boxed_1059_ = lean_unbox(v_isMeta_1054_);
v_res_1060_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_mod_1053_, v_isMeta_boxed_1059_, v_hint_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(lean_object* v___x_1061_, lean_object* v_declName_1062_, lean_object* v_as_1063_, size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_b_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_declName_1062_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_b_1066_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v_modules_1073_; lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v_toImport_1077_; lean_object* v_module_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1072_ = l_Lean_Environment_header(v___x_1061_);
v_modules_1073_ = lean_ctor_get(v___x_1072_, 3);
lean_inc_ref(v_modules_1073_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1075_ = lean_array_uget_borrowed(v_as_1063_, v_i_1065_);
v___x_1076_ = lean_array_get(v___x_1074_, v_modules_1073_, v_a_1075_);
lean_dec_ref(v_modules_1073_);
v_toImport_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_toImport_1077_);
lean_dec(v___x_1076_);
v_module_1078_ = lean_ctor_get(v_toImport_1077_, 0);
lean_inc(v_module_1078_);
lean_dec_ref(v_toImport_1077_);
v___x_1079_ = 0;
lean_inc(v_declName_1062_);
v___x_1080_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_1078_, v___x_1079_, v_declName_1062_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; 
lean_dec_ref_known(v___x_1080_, 1);
v___x_1081_ = lean_box(0);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1065_, v___x_1082_);
v_i_1065_ = v___x_1083_;
v_b_1066_ = v___x_1081_;
goto _start;
}
else
{
lean_dec(v_declName_1062_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v___x_1085_, lean_object* v_declName_1086_, lean_object* v_as_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
size_t v_sz_boxed_1094_; size_t v_i_boxed_1095_; lean_object* v_res_1096_; 
v_sz_boxed_1094_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1095_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v___x_1085_, v_declName_1086_, v_as_1087_, v_sz_boxed_1094_, v_i_boxed_1095_, v_b_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v_as_1087_);
lean_dec_ref(v___x_1085_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1));
v___x_1100_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0));
v___x_1101_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(lean_object* v_declName_1104_, uint8_t v_isMeta_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_env_1113_; lean_object* v___y_1115_; lean_object* v___x_1128_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1113_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1113_);
lean_dec(v___x_1109_);
v___x_1128_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1113_, v_declName_1104_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_dec_ref(v_env_1113_);
lean_dec(v_declName_1104_);
goto v___jp_1110_;
}
else
{
lean_object* v_val_1129_; lean_object* v___x_1130_; lean_object* v_modules_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_val_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_Environment_header(v_env_1113_);
v_modules_1131_ = lean_ctor_get(v___x_1130_, 3);
lean_inc_ref(v_modules_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = lean_array_get_size(v_modules_1131_);
v___x_1133_ = lean_nat_dec_lt(v_val_1129_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_modules_1131_);
lean_dec(v_val_1129_);
lean_dec_ref(v_env_1113_);
lean_dec(v_declName_1104_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1134_; lean_object* v_env_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___y_1139_; 
v___x_1134_ = lean_st_ref_get(v___y_1107_);
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_ref(v_env_1135_);
lean_dec(v___x_1134_);
v___x_1136_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2);
v___x_1137_ = lean_array_fget(v_modules_1131_, v_val_1129_);
lean_dec(v_val_1129_);
lean_dec_ref(v_modules_1131_);
if (v_isMeta_1105_ == 0)
{
lean_dec_ref(v_env_1135_);
v___y_1139_ = v_isMeta_1105_;
goto v___jp_1138_;
}
else
{
uint8_t v___x_1150_; 
lean_inc(v_declName_1104_);
v___x_1150_ = l_Lean_isMarkedMeta(v_env_1135_, v_declName_1104_);
if (v___x_1150_ == 0)
{
v___y_1139_ = v_isMeta_1105_;
goto v___jp_1138_;
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
v___y_1139_ = v___x_1151_;
goto v___jp_1138_;
}
}
v___jp_1138_:
{
lean_object* v_toImport_1140_; lean_object* v_module_1141_; lean_object* v___x_1142_; 
v_toImport_1140_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_toImport_1140_);
lean_dec(v___x_1137_);
v_module_1141_ = lean_ctor_get(v_toImport_1140_, 0);
lean_inc(v_module_1141_);
lean_dec_ref(v_toImport_1140_);
lean_inc(v_declName_1104_);
v___x_1142_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_1141_, v___y_1139_, v_declName_1104_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1142_, 1);
v___x_1143_ = l_Lean_indirectModUseExt;
v___x_1144_ = lean_box(1);
v___x_1145_ = lean_box(0);
lean_inc_ref(v_env_1113_);
v___x_1146_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1136_, v___x_1143_, v_env_1113_, v___x_1144_, v___x_1145_);
v___x_1147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_1146_, v_declName_1104_);
lean_dec(v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3));
v___y_1115_ = v___x_1148_;
goto v___jp_1114_;
}
else
{
lean_object* v_val_1149_; 
v_val_1149_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1149_);
lean_dec_ref_known(v___x_1147_, 1);
v___y_1115_ = v_val_1149_;
goto v___jp_1114_;
}
}
else
{
lean_dec_ref(v_env_1113_);
lean_dec(v_declName_1104_);
return v___x_1142_;
}
}
}
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_box(0);
v_sz_1117_ = lean_array_size(v___y_1115_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v_env_1113_, v_declName_1104_, v___y_1115_, v_sz_1117_, v___x_1118_, v___x_1116_, v___y_1106_, v___y_1107_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_env_1113_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1119_, 0);
lean_dec(v_unused_1127_);
v___x_1121_ = v___x_1119_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v___x_1119_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1116_);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1116_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___boxed(lean_object* v_declName_1152_, lean_object* v_isMeta_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v_isMeta_boxed_1157_; lean_object* v_res_1158_; 
v_isMeta_boxed_1157_ = lean_unbox(v_isMeta_1153_);
v_res_1158_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_declName_1152_, v_isMeta_boxed_1157_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_x_1162_, lean_object* v_stx_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1221_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1221_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1221_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v_infoState_1173_; uint8_t v_enabled_1174_; lean_object* v___x_1175_; 
v___x_1172_ = lean_st_ref_get(v___y_1165_);
v_infoState_1173_ = lean_ctor_get(v___x_1172_, 7);
lean_inc_ref(v_infoState_1173_);
lean_dec(v___x_1172_);
v_enabled_1174_ = lean_ctor_get_uint8(v_infoState_1173_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1173_);
v___x_1175_ = l_Lean_Syntax_getId(v_a_1168_);
if (v_enabled_1174_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v_a_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1175_);
v___x_1177_ = v___x_1170_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = l_Lean_Name_getRoot(v___x_1175_);
v___x_1180_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1181_ = lean_name_eq(v___x_1179_, v___x_1180_);
lean_dec(v___x_1179_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_a_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1175_);
v___x_1183_ = v___x_1170_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1175_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1185_ = lean_st_ref_get(v___y_1165_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_box(0);
lean_inc(v___x_1175_);
v___x_1188_ = l_Lean_Name_replacePrefix(v___x_1175_, v___x_1180_, v___x_1187_);
lean_inc(v___x_1188_);
v___x_1189_ = l_Lean_Environment_contains(v_env_1186_, v___x_1188_, v_enabled_1174_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
lean_dec(v___x_1188_);
lean_dec(v_a_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1175_);
v___x_1191_ = v___x_1170_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1175_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
uint8_t v___x_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1170_);
v___x_1193_ = 0;
lean_inc(v___x_1188_);
v___x_1194_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v___x_1188_, v___x_1193_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref_known(v___x_1194_, 1);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_a_1168_, v___x_1188_, v___x_1195_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1204_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1175_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1175_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v___x_1175_);
v_a_1205_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1196_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1196_);
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
lean_dec(v___x_1188_);
lean_dec(v___x_1175_);
lean_dec(v_a_1168_);
v_a_1213_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1194_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1194_);
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
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1167_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1167_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_x_1230_, lean_object* v_stx_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_x_8423__boxed_1235_; lean_object* v_res_1236_; 
v_x_8423__boxed_1235_ = lean_unbox(v_x_1230_);
v_res_1236_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_x_8423__boxed_1235_, v_stx_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1270_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1271_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1269_, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_1275_, v_a_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_1278_, lean_object* v_m_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_1278_, v_m_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_m_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11(lean_object* v_t_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v_t_1282_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___boxed(lean_object* v_t_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11(v_t_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1293_, v_x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1296_, v_x_1297_, v_x_1298_);
lean_dec_ref(v_x_1298_);
lean_dec_ref(v_x_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_1302_, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_a_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_1305_, v_a_1306_, v_x_1307_);
lean_dec(v_x_1307_);
lean_dec(v_a_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1309_, lean_object* v_x_1310_, size_t v_x_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_1310_, v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
size_t v_x_8689__boxed_1318_; uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_x_8689__boxed_1318_ = lean_unbox_usize(v_x_1316_);
lean_dec(v_x_1316_);
v_res_1319_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1314_, v_x_1315_, v_x_8689__boxed_1318_, v_x_1317_);
lean_dec_ref(v_x_1317_);
lean_dec_ref(v_x_1315_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11(lean_object* v_00_u03b1_1321_, lean_object* v_constName_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_constName_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11(v_00_u03b1_1327_, v_constName_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1333_, lean_object* v_keys_1334_, lean_object* v_vals_1335_, lean_object* v_heq_1336_, lean_object* v_i_1337_, lean_object* v_k_1338_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1334_, v_i_1337_, v_k_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1340_, lean_object* v_keys_1341_, lean_object* v_vals_1342_, lean_object* v_heq_1343_, lean_object* v_i_1344_, lean_object* v_k_1345_){
_start:
{
uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1340_, v_keys_1341_, v_vals_1342_, v_heq_1343_, v_i_1344_, v_k_1345_);
lean_dec_ref(v_k_1345_);
lean_dec_ref(v_vals_1342_);
lean_dec_ref(v_keys_1341_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15(lean_object* v_00_u03b1_1348_, lean_object* v_ref_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_1349_, v_constName_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_ref_1356_, lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15(v_00_u03b1_1355_, v_ref_1356_, v_constName_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_ref_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17(lean_object* v_00_u03b1_1362_, lean_object* v_ref_1363_, lean_object* v_msg_1364_, lean_object* v_declHint_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_1363_, v_msg_1364_, v_declHint_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_ref_1371_, lean_object* v_msg_1372_, lean_object* v_declHint_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17(v_00_u03b1_1370_, v_ref_1371_, v_msg_1372_, v_declHint_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v_ref_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_1378_, lean_object* v_declHint_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_1378_, v_declHint_1379_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_1384_, lean_object* v_declHint_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19(v_msg_1384_, v_declHint_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_1390_, lean_object* v_ref_1391_, lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_1391_, v_msg_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_ref_1398_, lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19(v_00_u03b1_1397_, v_ref_1398_, v_msg_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_ref_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21(lean_object* v_00_u03b1_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21(v_00_u03b1_1410_, v_msg_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1419_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1420_ = l_Lean_addBuiltinDocString(v___x_1418_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1450_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1451_ = l_Lean_addBuiltinDeclarationRanges(v___x_1449_, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1482_, uint8_t v___x_1483_, lean_object* v_id_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1488_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1482_, v___x_1483_);
v___x_1490_ = lean_string_append(v___x_1488_, v___x_1489_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
v___x_1493_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1484_, v___x_1492_, v___y_1486_, v___y_1487_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v_id_1496_, lean_object* v_x_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_2590__boxed_1500_; lean_object* v_res_1501_; 
v___x_2590__boxed_1500_ = lean_unbox(v___x_1495_);
v_res_1501_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1494_, v___x_2590__boxed_1500_, v_id_1496_, v_x_1497_, v___y_1498_, v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v_x_1497_);
lean_dec(v_id_1496_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1512_ = l_String_toRawSubstring_x27(v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___y_1520_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1516_);
v___x_1540_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v_x_1516_);
v___x_1541_ = lean_box(1);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_a_1518_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; lean_object* v_id_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v_id_1544_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1543_);
lean_dec(v_x_1516_);
v___x_1545_ = l_Lean_TSyntax_getId(v_id_1544_);
lean_inc(v___x_1545_);
v___x_1546_ = l_Lean_Macro_resolveGlobalName(v___x_1545_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
if (lean_obj_tag(v_a_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1546_, 2);
v___x_1549_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1545_, v___x_1540_);
v___x_1551_ = lean_string_append(v___x_1549_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_1553_ = lean_string_append(v___x_1551_, v___x_1552_);
v___x_1554_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1544_, v___x_1553_, v_a_1517_, v_a_1548_);
lean_dec(v_id_1544_);
v___y_1520_ = v___x_1554_;
goto v___jp_1519_;
}
else
{
lean_object* v_head_1555_; lean_object* v_snd_1556_; 
v_head_1555_ = lean_ctor_get(v_a_1547_, 0);
v_snd_1556_ = lean_ctor_get(v_head_1555_, 1);
if (lean_obj_tag(v_snd_1556_) == 0)
{
lean_object* v_tail_1557_; 
v_tail_1557_ = lean_ctor_get(v_a_1547_, 1);
if (lean_obj_tag(v_tail_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1583_; 
lean_inc(v_head_1555_);
lean_dec_ref_known(v_a_1547_, 2);
lean_dec(v___x_1545_);
v_a_1558_ = lean_ctor_get(v___x_1546_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1584_);
v___x_1560_ = v___x_1546_;
v_isShared_1561_ = v_isSharedCheck_1583_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1546_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1583_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_fst_1562_; lean_object* v_quotContext_1563_; lean_object* v_currMacroScope_1564_; lean_object* v_ref_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v_fst_1562_ = lean_ctor_get(v_head_1555_, 0);
lean_inc(v_fst_1562_);
lean_dec(v_head_1555_);
v_quotContext_1563_ = lean_ctor_get(v_a_1517_, 1);
v_currMacroScope_1564_ = lean_ctor_get(v_a_1517_, 2);
v_ref_1565_ = lean_ctor_get(v_a_1517_, 5);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_SourceInfo_fromRef(v_ref_1565_, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1569_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1570_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1564_);
lean_inc(v_quotContext_1563_);
v___x_1571_ = l_Lean_addMacroScope(v_quotContext_1563_, v___x_1570_, v_currMacroScope_1564_);
v___x_1572_ = lean_box(0);
lean_inc_n(v___x_1567_, 2);
v___x_1573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1567_);
lean_ctor_set(v___x_1573_, 1, v___x_1569_);
lean_ctor_set(v___x_1573_, 2, v___x_1571_);
lean_ctor_set(v___x_1573_, 3, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_1575_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1576_ = l_Lean_Name_append(v___x_1575_, v_fst_1562_);
v___x_1577_ = l_Lean_mkIdentFrom(v_id_1544_, v___x_1576_, v___x_1540_);
lean_dec(v_id_1544_);
v___x_1578_ = l_Lean_Syntax_node1(v___x_1567_, v___x_1574_, v___x_1577_);
v___x_1579_ = l_Lean_Syntax_node2(v___x_1567_, v___x_1568_, v___x_1573_, v___x_1578_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1579_);
v___x_1581_ = v___x_1560_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_a_1558_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1546_, 2);
v___x_1586_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1545_, v___x_1540_, v_id_1544_, v_a_1547_, v_a_1517_, v_a_1585_);
lean_dec_ref_known(v_a_1547_, 2);
lean_dec(v_id_1544_);
v___y_1520_ = v___x_1586_;
goto v___jp_1519_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1546_, 2);
v___x_1588_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1545_, v___x_1540_, v_id_1544_, v_a_1547_, v_a_1517_, v_a_1587_);
lean_dec_ref_known(v_a_1547_, 2);
lean_dec(v_id_1544_);
v___y_1520_ = v___x_1588_;
goto v___jp_1519_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v___x_1545_);
lean_dec(v_id_1544_);
v_a_1589_ = lean_ctor_get(v___x_1546_, 0);
v_a_1590_ = lean_ctor_get(v___x_1546_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1546_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
lean_dec(v___x_1546_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
v___jp_1519_:
{
if (lean_obj_tag(v___y_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1521_ = lean_ctor_get(v___y_1520_, 0);
v_a_1522_ = lean_ctor_get(v___y_1520_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___y_1520_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___y_1520_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_inc(v_a_1521_);
lean_dec(v___y_1520_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_a_1530_ = lean_ctor_get(v___y_1520_, 0);
v_a_1531_ = lean_ctor_get(v___y_1520_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___y_1520_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___y_1520_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_inc(v_a_1530_);
lean_dec(v___y_1520_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1530_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1598_, v_a_1599_, v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1602_){
_start:
{
lean_object* v_subExpr_1604_; lean_object* v_expr_1605_; lean_object* v___x_1606_; 
v_subExpr_1604_ = lean_ctor_get(v___y_1602_, 3);
v_expr_1605_ = lean_ctor_get(v_subExpr_1604_, 0);
lean_inc_ref(v_expr_1605_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_expr_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1607_);
lean_dec_ref(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1610_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1626_, lean_object* v_us_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1629_ = l_Lean_Name_append(v___x_1628_, v_c_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1630_, lean_object* v_us_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1630_, v_us_1631_);
lean_dec(v_us_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1638_);
lean_dec(v_x_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1750_; 
v___x_1674_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1667_);
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1750_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1750_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
switch(lean_obj_tag(v_a_1675_))
{
case 0:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec_ref_known(v_a_1675_, 1);
v___x_1679_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
case 1:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_dec_ref_known(v_a_1675_, 1);
v___x_1683_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1683_);
v___x_1685_ = v___x_1677_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
case 2:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_dec_ref_known(v_a_1675_, 1);
v___x_1687_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1687_);
v___x_1689_ = v___x_1677_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
case 3:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_dec_ref_known(v_a_1675_, 1);
v___x_1691_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1691_);
v___x_1693_ = v___x_1677_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
case 4:
{
lean_object* v_declName_1695_; lean_object* v_us_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_declName_1695_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_declName_1695_);
v_us_1696_ = lean_ctor_get(v_a_1675_, 1);
lean_inc(v_us_1696_);
lean_dec_ref_known(v_a_1675_, 2);
v___x_1697_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1695_, v_us_1696_);
lean_dec(v_us_1696_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1697_);
v___x_1699_ = v___x_1677_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
case 5:
{
lean_object* v_fn_1701_; lean_object* v___x_1702_; 
v_fn_1701_ = lean_ctor_get(v_a_1675_, 0);
lean_inc_ref(v_fn_1701_);
lean_dec_ref_known(v_a_1675_, 2);
v___x_1702_ = l_Lean_Expr_getAppFn(v_fn_1701_);
lean_dec_ref(v_fn_1701_);
if (lean_obj_tag(v___x_1702_) == 4)
{
lean_object* v_declName_1703_; lean_object* v_us_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v_declName_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_declName_1703_);
v_us_1704_ = lean_ctor_get(v___x_1702_, 1);
lean_inc(v_us_1704_);
lean_dec_ref_known(v___x_1702_, 2);
v___x_1705_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1703_, v_us_1704_);
lean_dec(v_us_1704_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1705_);
v___x_1707_ = v___x_1677_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
lean_dec_ref(v___x_1702_);
v___x_1709_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1709_);
v___x_1711_ = v___x_1677_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
case 6:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_dec_ref_known(v_a_1675_, 3);
v___x_1713_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1713_);
v___x_1715_ = v___x_1677_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
case 7:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec_ref_known(v_a_1675_, 3);
v___x_1717_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1717_);
v___x_1719_ = v___x_1677_;
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
case 8:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_dec_ref_known(v_a_1675_, 4);
v___x_1721_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1721_);
v___x_1723_ = v___x_1677_;
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
case 9:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec_ref_known(v_a_1675_, 1);
v___x_1725_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1725_);
v___x_1727_ = v___x_1677_;
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
case 10:
{
lean_object* v_data_1729_; 
v_data_1729_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_data_1729_);
lean_dec_ref_known(v_a_1675_, 2);
if (lean_obj_tag(v_data_1729_) == 1)
{
lean_object* v_tail_1730_; 
v_tail_1730_ = lean_ctor_get(v_data_1729_, 1);
if (lean_obj_tag(v_tail_1730_) == 0)
{
lean_object* v_head_1731_; lean_object* v_fst_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v_head_1731_ = lean_ctor_get(v_data_1729_, 0);
lean_inc(v_head_1731_);
lean_dec_ref_known(v_data_1729_, 2);
v_fst_1732_ = lean_ctor_get(v_head_1731_, 0);
lean_inc(v_fst_1732_);
lean_dec(v_head_1731_);
v___x_1733_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1734_ = l_Lean_Name_append(v___x_1733_, v_fst_1732_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1734_);
v___x_1736_ = v___x_1677_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1729_);
lean_dec_ref_known(v_data_1729_, 2);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1738_);
v___x_1740_ = v___x_1677_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1729_);
lean_dec(v_data_1729_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1742_);
v___x_1744_ = v___x_1677_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
default: 
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
lean_dec_ref_known(v_a_1675_, 3);
v___x_1746_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1746_);
v___x_1748_ = v___x_1677_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1759_, lean_object* v_k_1760_, lean_object* v_v_1761_){
_start:
{
lean_object* v_map_1762_; uint8_t v_hasTrace_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1776_; 
v_map_1762_ = lean_ctor_get(v_o_1759_, 0);
v_hasTrace_1763_ = lean_ctor_get_uint8(v_o_1759_, sizeof(void*)*1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_o_1759_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1765_ = v_o_1759_;
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_map_1762_);
lean_dec(v_o_1759_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; 
lean_inc(v_k_1760_);
v___x_1767_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1760_, v_v_1761_, v_map_1762_);
if (v_hasTrace_1763_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_1769_ = l_Lean_Name_isPrefixOf(v___x_1768_, v_k_1760_);
lean_dec(v_k_1760_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1767_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*1, v___x_1769_);
return v___x_1771_;
}
}
else
{
lean_object* v___x_1774_; 
lean_dec(v_k_1760_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1774_ = v___x_1765_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*1, v_hasTrace_1763_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1777_){
_start:
{
lean_object* v_subExpr_1779_; lean_object* v_pos_1780_; lean_object* v___x_1781_; 
v_subExpr_1779_ = lean_ctor_get(v___y_1777_, 3);
v_pos_1780_ = lean_ctor_get(v_subExpr_1779_, 1);
lean_inc(v_pos_1780_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_pos_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1782_);
lean_dec_ref(v___y_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1785_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1801_, lean_object* v_k_1802_){
_start:
{
if (lean_obj_tag(v_t_1801_) == 0)
{
lean_object* v_k_1803_; lean_object* v_v_1804_; lean_object* v_l_1805_; lean_object* v_r_1806_; uint8_t v___x_1807_; 
v_k_1803_ = lean_ctor_get(v_t_1801_, 1);
v_v_1804_ = lean_ctor_get(v_t_1801_, 2);
v_l_1805_ = lean_ctor_get(v_t_1801_, 3);
v_r_1806_ = lean_ctor_get(v_t_1801_, 4);
v___x_1807_ = lean_nat_dec_lt(v_k_1802_, v_k_1803_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_nat_dec_eq(v_k_1802_, v_k_1803_);
if (v___x_1808_ == 0)
{
v_t_1801_ = v_r_1806_;
goto _start;
}
else
{
lean_object* v___x_1810_; 
lean_inc(v_v_1804_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_v_1804_);
return v___x_1810_;
}
}
else
{
v_t_1801_ = v_l_1805_;
goto _start;
}
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_box(0);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1813_, lean_object* v_k_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1813_, v_k_1814_);
lean_dec(v_k_1814_);
lean_dec(v_t_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1816_, lean_object* v_x_1817_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
lean_object* v_k_1819_; lean_object* v_v_1820_; lean_object* v_l_1821_; lean_object* v_r_1822_; lean_object* v___x_1823_; lean_object* v_a_1824_; lean_object* v_a_1825_; lean_object* v___x_1826_; 
v_k_1819_ = lean_ctor_get(v_x_1817_, 1);
lean_inc(v_k_1819_);
v_v_1820_ = lean_ctor_get(v_x_1817_, 2);
lean_inc(v_v_1820_);
v_l_1821_ = lean_ctor_get(v_x_1817_, 3);
lean_inc(v_l_1821_);
v_r_1822_ = lean_ctor_get(v_x_1817_, 4);
lean_inc(v_r_1822_);
lean_dec_ref_known(v_x_1817_, 5);
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1816_, v_l_1821_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v_a_1825_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_a_1825_);
lean_dec(v_a_1824_);
v___x_1826_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1825_, v_k_1819_, v_v_1820_);
v_init_1816_ = v___x_1826_;
v_x_1817_ = v_r_1822_;
goto _start;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_init_1816_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1830_, lean_object* v_x_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1830_, v_x_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_options_1841_; lean_object* v___x_1842_; lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1864_; 
v_options_1841_ = lean_ctor_get(v_a_1838_, 2);
v___x_1842_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1834_);
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1864_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1864_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_optionsPerPos_1847_; lean_object* v___x_1848_; 
v_optionsPerPos_1847_ = lean_ctor_get(v_a_1834_, 0);
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1847_, v_a_1843_);
lean_dec(v_a_1843_);
if (lean_obj_tag(v___x_1848_) == 1)
{
lean_object* v_val_1849_; lean_object* v_map_1850_; lean_object* v___x_1851_; lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
lean_del_object(v___x_1845_);
v_val_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v_map_1850_ = lean_ctor_get(v_val_1849_, 0);
lean_inc(v_map_1850_);
lean_dec(v_val_1849_);
lean_inc_ref(v_options_1841_);
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_options_1841_, v_map_1850_);
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_a_1856_; lean_object* v___x_1858_; 
v_a_1856_ = lean_ctor_get(v_a_1852_, 0);
lean_inc(v_a_1856_);
lean_dec(v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_a_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v___x_1862_; 
lean_dec(v___x_1848_);
lean_inc_ref(v_options_1841_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_options_1841_);
v___x_1862_ = v___x_1845_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_options_1841_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1873_, lean_object* v_t_1874_, lean_object* v_k_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1874_, v_k_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1877_, lean_object* v_t_1878_, lean_object* v_k_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1877_, v_t_1878_, v_k_1879_);
lean_dec(v_k_1879_);
lean_dec(v_t_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1881_, lean_object* v_x_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1881_, v_x_1882_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1891_, v_x_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_apply_1(v_opt_1901_, v_a_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_opt_1901_);
v_a_1919_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1909_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1909_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_1936_, lean_object* v_opt_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_opt_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_1946_, v_opt_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_1956_, lean_object* v_d_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1956_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; uint8_t v___x_1967_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = lean_unbox(v_a_1966_);
lean_dec(v_a_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_d_1957_);
v___x_1968_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; 
lean_inc(v_a_1963_);
lean_inc_ref(v_a_1962_);
lean_inc(v_a_1961_);
lean_inc_ref(v_a_1960_);
lean_inc(v_a_1959_);
lean_inc_ref(v_a_1958_);
v___x_1969_ = lean_apply_7(v_d_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, lean_box(0));
return v___x_1969_;
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_d_1957_);
v_a_1970_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1965_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1965_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_1978_, lean_object* v_d_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_1978_, v_d_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_1988_, lean_object* v_d_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1988_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; uint8_t v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_inc(v_a_1995_);
lean_inc_ref(v_a_1994_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
v___x_2000_ = lean_apply_7(v_d_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, lean_box(0));
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; 
lean_dec_ref(v_d_1989_);
v___x_2001_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2001_;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_d_1989_);
v_a_2002_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1997_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1997_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2010_, lean_object* v_d_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2010_, v_d_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2020_, lean_object* v_v_2021_, lean_object* v_t_2022_){
_start:
{
if (lean_obj_tag(v_t_2022_) == 0)
{
lean_object* v_size_2023_; lean_object* v_k_2024_; lean_object* v_v_2025_; lean_object* v_l_2026_; lean_object* v_r_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2308_; 
v_size_2023_ = lean_ctor_get(v_t_2022_, 0);
v_k_2024_ = lean_ctor_get(v_t_2022_, 1);
v_v_2025_ = lean_ctor_get(v_t_2022_, 2);
v_l_2026_ = lean_ctor_get(v_t_2022_, 3);
v_r_2027_ = lean_ctor_get(v_t_2022_, 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_t_2022_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2029_ = v_t_2022_;
v_isShared_2030_ = v_isSharedCheck_2308_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_r_2027_);
lean_inc(v_l_2026_);
lean_inc(v_v_2025_);
lean_inc(v_k_2024_);
lean_inc(v_size_2023_);
lean_dec(v_t_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2308_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_nat_dec_lt(v_k_2020_, v_k_2024_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_nat_dec_eq(v_k_2020_, v_k_2024_);
if (v___x_2032_ == 0)
{
lean_object* v_impl_2033_; lean_object* v___x_2034_; 
lean_dec(v_size_2023_);
v_impl_2033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2020_, v_v_2021_, v_r_2027_);
v___x_2034_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2026_) == 0)
{
lean_object* v_size_2035_; lean_object* v_size_2036_; lean_object* v_k_2037_; lean_object* v_v_2038_; lean_object* v_l_2039_; lean_object* v_r_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_size_2035_ = lean_ctor_get(v_l_2026_, 0);
v_size_2036_ = lean_ctor_get(v_impl_2033_, 0);
lean_inc(v_size_2036_);
v_k_2037_ = lean_ctor_get(v_impl_2033_, 1);
lean_inc(v_k_2037_);
v_v_2038_ = lean_ctor_get(v_impl_2033_, 2);
lean_inc(v_v_2038_);
v_l_2039_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2039_);
v_r_2040_ = lean_ctor_get(v_impl_2033_, 4);
lean_inc(v_r_2040_);
v___x_2041_ = lean_unsigned_to_nat(3u);
v___x_2042_ = lean_nat_mul(v___x_2041_, v_size_2035_);
v___x_2043_ = lean_nat_dec_lt(v___x_2042_, v_size_2036_);
lean_dec(v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_r_2040_);
lean_dec(v_l_2039_);
lean_dec(v_v_2038_);
lean_dec(v_k_2037_);
v___x_2044_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2045_ = lean_nat_add(v___x_2044_, v_size_2036_);
lean_dec(v_size_2036_);
lean_dec(v___x_2044_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_impl_2033_);
lean_ctor_set(v___x_2029_, 0, v___x_2045_);
v___x_2047_ = v___x_2029_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_impl_2033_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2112_; 
v_isSharedCheck_2112_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2113_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_impl_2033_, 2);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_impl_2033_, 1);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2117_);
v___x_2050_ = v_impl_2033_;
v_isShared_2051_ = v_isSharedCheck_2112_;
goto v_resetjp_2049_;
}
else
{
lean_dec(v_impl_2033_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2112_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_size_2052_; lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v_l_2055_; lean_object* v_r_2056_; lean_object* v_size_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_size_2052_ = lean_ctor_get(v_l_2039_, 0);
v_k_2053_ = lean_ctor_get(v_l_2039_, 1);
v_v_2054_ = lean_ctor_get(v_l_2039_, 2);
v_l_2055_ = lean_ctor_get(v_l_2039_, 3);
v_r_2056_ = lean_ctor_get(v_l_2039_, 4);
v_size_2057_ = lean_ctor_get(v_r_2040_, 0);
v___x_2058_ = lean_unsigned_to_nat(2u);
v___x_2059_ = lean_nat_mul(v___x_2058_, v_size_2057_);
v___x_2060_ = lean_nat_dec_lt(v_size_2052_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2088_; 
lean_inc(v_r_2056_);
lean_inc(v_l_2055_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_l_2039_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2089_ = lean_ctor_get(v_l_2039_, 4);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_l_2039_, 3);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_l_2039_, 2);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_l_2039_, 1);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_l_2039_, 0);
lean_dec(v_unused_2093_);
v___x_2062_ = v_l_2039_;
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v_l_2039_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2078_; 
v___x_2064_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2065_ = lean_nat_add(v___x_2064_, v_size_2036_);
lean_dec(v_size_2036_);
if (lean_obj_tag(v_l_2055_) == 0)
{
lean_object* v_size_2086_; 
v_size_2086_ = lean_ctor_get(v_l_2055_, 0);
lean_inc(v_size_2086_);
v___y_2078_ = v_size_2086_;
goto v___jp_2077_;
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___y_2078_ = v___x_2087_;
goto v___jp_2077_;
}
v___jp_2066_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_nat_add(v___y_2067_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec(v___y_2067_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v_r_2040_);
lean_ctor_set(v___x_2062_, 3, v_r_2056_);
lean_ctor_set(v___x_2062_, 2, v_v_2038_);
lean_ctor_set(v___x_2062_, 1, v_k_2037_);
lean_ctor_set(v___x_2062_, 0, v___x_2070_);
v___x_2072_ = v___x_2062_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_r_2040_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v___x_2072_);
lean_ctor_set(v___x_2050_, 3, v___y_2068_);
lean_ctor_set(v___x_2050_, 2, v_v_2054_);
lean_ctor_set(v___x_2050_, 1, v_k_2053_);
lean_ctor_set(v___x_2050_, 0, v___x_2065_);
v___x_2074_ = v___x_2050_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v___y_2068_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
v___jp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_nat_add(v___x_2064_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec(v___x_2064_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_2055_);
lean_ctor_set(v___x_2029_, 0, v___x_2079_);
v___x_2081_ = v___x_2029_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_l_2055_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_nat_add(v___x_2034_, v_size_2057_);
if (lean_obj_tag(v_r_2056_) == 0)
{
lean_object* v_size_2083_; 
v_size_2083_ = lean_ctor_get(v_r_2056_, 0);
lean_inc(v_size_2083_);
v___y_2067_ = v___x_2082_;
v___y_2068_ = v___x_2081_;
v___y_2069_ = v_size_2083_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___y_2067_ = v___x_2082_;
v___y_2068_ = v___x_2081_;
v___y_2069_ = v___x_2084_;
goto v___jp_2066_;
}
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
lean_del_object(v___x_2029_);
v___x_2094_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2095_ = lean_nat_add(v___x_2094_, v_size_2036_);
lean_dec(v_size_2036_);
v___x_2096_ = lean_nat_add(v___x_2094_, v_size_2052_);
lean_dec(v___x_2094_);
lean_inc_ref(v_l_2026_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v_l_2039_);
lean_ctor_set(v___x_2050_, 3, v_l_2026_);
lean_ctor_set(v___x_2050_, 2, v_v_2025_);
lean_ctor_set(v___x_2050_, 1, v_k_2024_);
lean_ctor_set(v___x_2050_, 0, v___x_2096_);
v___x_2098_ = v___x_2050_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_l_2039_);
v___x_2098_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_isSharedCheck_2105_ = !lean_is_exclusive(v_l_2026_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; lean_object* v_unused_2107_; lean_object* v_unused_2108_; lean_object* v_unused_2109_; lean_object* v_unused_2110_; 
v_unused_2106_ = lean_ctor_get(v_l_2026_, 4);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_l_2026_, 3);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_l_2026_, 2);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_l_2026_, 1);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_l_2026_, 0);
lean_dec(v_unused_2110_);
v___x_2100_ = v_l_2026_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_dec(v_l_2026_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 4, v_r_2040_);
lean_ctor_set(v___x_2100_, 3, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v_v_2038_);
lean_ctor_set(v___x_2100_, 1, v_k_2037_);
lean_ctor_set(v___x_2100_, 0, v___x_2095_);
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_r_2040_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2118_; 
v_l_2118_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2118_);
if (lean_obj_tag(v_l_2118_) == 0)
{
lean_object* v_r_2119_; lean_object* v_k_2120_; lean_object* v_v_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2144_; 
v_r_2119_ = lean_ctor_get(v_impl_2033_, 4);
v_k_2120_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2121_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2145_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2146_);
v___x_2123_ = v_impl_2033_;
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_r_2119_);
lean_inc(v_v_2121_);
lean_inc(v_k_2120_);
lean_dec(v_impl_2033_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_k_2125_; lean_object* v_v_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2140_; 
v_k_2125_ = lean_ctor_get(v_l_2118_, 1);
v_v_2126_ = lean_ctor_get(v_l_2118_, 2);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_l_2118_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; 
v_unused_2141_ = lean_ctor_get(v_l_2118_, 4);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_l_2118_, 3);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_l_2118_, 0);
lean_dec(v_unused_2143_);
v___x_2128_ = v_l_2118_;
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_v_2126_);
lean_inc(v_k_2125_);
lean_dec(v_l_2118_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2119_, 2);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v_r_2119_);
lean_ctor_set(v___x_2128_, 3, v_r_2119_);
lean_ctor_set(v___x_2128_, 2, v_v_2025_);
lean_ctor_set(v___x_2128_, 1, v_k_2024_);
lean_ctor_set(v___x_2128_, 0, v___x_2034_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_r_2119_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_r_2119_);
v___x_2132_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
lean_inc(v_r_2119_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 3, v_r_2119_);
lean_ctor_set(v___x_2123_, 0, v___x_2034_);
v___x_2134_ = v___x_2123_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_r_2119_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_r_2119_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2134_);
lean_ctor_set(v___x_2029_, 3, v___x_2132_);
lean_ctor_set(v___x_2029_, 2, v_v_2126_);
lean_ctor_set(v___x_2029_, 1, v_k_2125_);
lean_ctor_set(v___x_2029_, 0, v___x_2130_);
v___x_2136_ = v___x_2029_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_2125_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_2126_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
else
{
lean_object* v_r_2147_; 
v_r_2147_ = lean_ctor_get(v_impl_2033_, 4);
lean_inc(v_r_2147_);
if (lean_obj_tag(v_r_2147_) == 0)
{
lean_object* v_k_2148_; lean_object* v_v_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2160_; 
v_k_2148_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2149_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2161_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2163_);
v___x_2151_ = v_impl_2033_;
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_v_2149_);
lean_inc(v_k_2148_);
lean_dec(v_impl_2033_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(3u);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v_l_2118_);
lean_ctor_set(v___x_2151_, 2, v_v_2025_);
lean_ctor_set(v___x_2151_, 1, v_k_2024_);
lean_ctor_set(v___x_2151_, 0, v___x_2034_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_l_2118_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_l_2118_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_r_2147_);
lean_ctor_set(v___x_2029_, 3, v___x_2155_);
lean_ctor_set(v___x_2029_, 2, v_v_2149_);
lean_ctor_set(v___x_2029_, 1, v_k_2148_);
lean_ctor_set(v___x_2029_, 0, v___x_2153_);
v___x_2157_ = v___x_2029_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_k_2148_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_v_2149_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_r_2147_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_unsigned_to_nat(2u);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_impl_2033_);
lean_ctor_set(v___x_2029_, 3, v_r_2147_);
lean_ctor_set(v___x_2029_, 0, v___x_2164_);
v___x_2166_ = v___x_2029_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_r_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_impl_2033_);
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
}
else
{
lean_object* v___x_2169_; 
lean_dec(v_v_2025_);
lean_dec(v_k_2024_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 2, v_v_2021_);
lean_ctor_set(v___x_2029_, 1, v_k_2020_);
v___x_2169_ = v___x_2029_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_size_2023_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_k_2020_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_v_2021_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_r_2027_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_impl_2171_; lean_object* v___x_2172_; 
lean_dec(v_size_2023_);
v_impl_2171_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2020_, v_v_2021_, v_l_2026_);
v___x_2172_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2027_) == 0)
{
lean_object* v_size_2173_; lean_object* v_size_2174_; lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v_l_2177_; lean_object* v_r_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_size_2173_ = lean_ctor_get(v_r_2027_, 0);
v_size_2174_ = lean_ctor_get(v_impl_2171_, 0);
lean_inc(v_size_2174_);
v_k_2175_ = lean_ctor_get(v_impl_2171_, 1);
lean_inc(v_k_2175_);
v_v_2176_ = lean_ctor_get(v_impl_2171_, 2);
lean_inc(v_v_2176_);
v_l_2177_ = lean_ctor_get(v_impl_2171_, 3);
lean_inc(v_l_2177_);
v_r_2178_ = lean_ctor_get(v_impl_2171_, 4);
lean_inc(v_r_2178_);
v___x_2179_ = lean_unsigned_to_nat(3u);
v___x_2180_ = lean_nat_mul(v___x_2179_, v_size_2173_);
v___x_2181_ = lean_nat_dec_lt(v___x_2180_, v_size_2174_);
lean_dec(v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_r_2178_);
lean_dec(v_l_2177_);
lean_dec(v_v_2176_);
lean_dec(v_k_2175_);
v___x_2182_ = lean_nat_add(v___x_2172_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2183_ = lean_nat_add(v___x_2182_, v_size_2173_);
lean_dec(v___x_2182_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 3, v_impl_2171_);
lean_ctor_set(v___x_2029_, 0, v___x_2183_);
v___x_2185_ = v___x_2029_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_impl_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_r_2027_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2252_; 
v_isSharedCheck_2252_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2253_ = lean_ctor_get(v_impl_2171_, 4);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_impl_2171_, 2);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_impl_2171_, 1);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2257_);
v___x_2188_ = v_impl_2171_;
v_isShared_2189_ = v_isSharedCheck_2252_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v_impl_2171_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2252_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_size_2190_; lean_object* v_size_2191_; lean_object* v_k_2192_; lean_object* v_v_2193_; lean_object* v_l_2194_; lean_object* v_r_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v_size_2190_ = lean_ctor_get(v_l_2177_, 0);
v_size_2191_ = lean_ctor_get(v_r_2178_, 0);
v_k_2192_ = lean_ctor_get(v_r_2178_, 1);
v_v_2193_ = lean_ctor_get(v_r_2178_, 2);
v_l_2194_ = lean_ctor_get(v_r_2178_, 3);
v_r_2195_ = lean_ctor_get(v_r_2178_, 4);
v___x_2196_ = lean_unsigned_to_nat(2u);
v___x_2197_ = lean_nat_mul(v___x_2196_, v_size_2190_);
v___x_2198_ = lean_nat_dec_lt(v_size_2191_, v___x_2197_);
lean_dec(v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2227_; 
lean_inc(v_r_2195_);
lean_inc(v_l_2194_);
lean_inc(v_v_2193_);
lean_inc(v_k_2192_);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_r_2178_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2228_ = lean_ctor_get(v_r_2178_, 4);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_2178_, 3);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_r_2178_, 2);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_r_2178_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_r_2178_, 0);
lean_dec(v_unused_2232_);
v___x_2200_ = v_r_2178_;
v_isShared_2201_ = v_isSharedCheck_2227_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_r_2178_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2227_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___x_2215_; lean_object* v___y_2217_; 
v___x_2202_ = lean_nat_add(v___x_2172_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2203_ = lean_nat_add(v___x_2202_, v_size_2173_);
lean_dec(v___x_2202_);
v___x_2215_ = lean_nat_add(v___x_2172_, v_size_2190_);
if (lean_obj_tag(v_l_2194_) == 0)
{
lean_object* v_size_2225_; 
v_size_2225_ = lean_ctor_get(v_l_2194_, 0);
lean_inc(v_size_2225_);
v___y_2217_ = v_size_2225_;
goto v___jp_2216_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___y_2217_ = v___x_2226_;
goto v___jp_2216_;
}
v___jp_2204_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_nat_add(v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec(v___y_2206_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 4, v_r_2027_);
lean_ctor_set(v___x_2200_, 3, v_r_2195_);
lean_ctor_set(v___x_2200_, 2, v_v_2025_);
lean_ctor_set(v___x_2200_, 1, v_k_2024_);
lean_ctor_set(v___x_2200_, 0, v___x_2208_);
v___x_2210_ = v___x_2200_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_r_2195_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_r_2027_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v___x_2210_);
lean_ctor_set(v___x_2188_, 3, v___y_2205_);
lean_ctor_set(v___x_2188_, 2, v_v_2193_);
lean_ctor_set(v___x_2188_, 1, v_k_2192_);
lean_ctor_set(v___x_2188_, 0, v___x_2203_);
v___x_2212_ = v___x_2188_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_k_2192_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2193_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v___y_2205_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
v___jp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_nat_add(v___x_2215_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec(v___x_2215_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_2194_);
lean_ctor_set(v___x_2029_, 3, v_l_2177_);
lean_ctor_set(v___x_2029_, 2, v_v_2176_);
lean_ctor_set(v___x_2029_, 1, v_k_2175_);
lean_ctor_set(v___x_2029_, 0, v___x_2218_);
v___x_2220_ = v___x_2029_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_l_2177_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_l_2194_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_nat_add(v___x_2172_, v_size_2173_);
if (lean_obj_tag(v_r_2195_) == 0)
{
lean_object* v_size_2222_; 
v_size_2222_ = lean_ctor_get(v_r_2195_, 0);
lean_inc(v_size_2222_);
v___y_2205_ = v___x_2220_;
v___y_2206_ = v___x_2221_;
v___y_2207_ = v_size_2222_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___x_2220_;
v___y_2206_ = v___x_2221_;
v___y_2207_ = v___x_2223_;
goto v___jp_2204_;
}
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_del_object(v___x_2029_);
v___x_2233_ = lean_nat_add(v___x_2172_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2234_ = lean_nat_add(v___x_2233_, v_size_2173_);
lean_dec(v___x_2233_);
v___x_2235_ = lean_nat_add(v___x_2172_, v_size_2173_);
v___x_2236_ = lean_nat_add(v___x_2235_, v_size_2191_);
lean_dec(v___x_2235_);
lean_inc_ref(v_r_2027_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v_r_2027_);
lean_ctor_set(v___x_2188_, 3, v_r_2178_);
lean_ctor_set(v___x_2188_, 2, v_v_2025_);
lean_ctor_set(v___x_2188_, 1, v_k_2024_);
lean_ctor_set(v___x_2188_, 0, v___x_2236_);
v___x_2238_ = v___x_2188_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_r_2027_);
v___x_2238_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_isSharedCheck_2245_ = !lean_is_exclusive(v_r_2027_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; 
v_unused_2246_ = lean_ctor_get(v_r_2027_, 4);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_r_2027_, 3);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_r_2027_, 2);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_r_2027_, 1);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_r_2027_, 0);
lean_dec(v_unused_2250_);
v___x_2240_ = v_r_2027_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v_r_2027_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v___x_2238_);
lean_ctor_set(v___x_2240_, 3, v_l_2177_);
lean_ctor_set(v___x_2240_, 2, v_v_2176_);
lean_ctor_set(v___x_2240_, 1, v_k_2175_);
lean_ctor_set(v___x_2240_, 0, v___x_2234_);
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_l_2177_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v___x_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2258_; 
v_l_2258_ = lean_ctor_get(v_impl_2171_, 3);
lean_inc(v_l_2258_);
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_r_2259_; lean_object* v_k_2260_; lean_object* v_v_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2272_; 
v_r_2259_ = lean_ctor_get(v_impl_2171_, 4);
v_k_2260_ = lean_ctor_get(v_impl_2171_, 1);
v_v_2261_ = lean_ctor_get(v_impl_2171_, 2);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; lean_object* v_unused_2274_; 
v_unused_2273_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2273_);
v_unused_2274_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2274_);
v___x_2263_ = v_impl_2171_;
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_r_2259_);
lean_inc(v_v_2261_);
lean_inc(v_k_2260_);
lean_dec(v_impl_2171_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2259_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 3, v_r_2259_);
lean_ctor_set(v___x_2263_, 2, v_v_2025_);
lean_ctor_set(v___x_2263_, 1, v_k_2024_);
lean_ctor_set(v___x_2263_, 0, v___x_2172_);
v___x_2267_ = v___x_2263_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_r_2259_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_r_2259_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2267_);
lean_ctor_set(v___x_2029_, 3, v_l_2258_);
lean_ctor_set(v___x_2029_, 2, v_v_2261_);
lean_ctor_set(v___x_2029_, 1, v_k_2260_);
lean_ctor_set(v___x_2029_, 0, v___x_2265_);
v___x_2269_ = v___x_2029_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_k_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_v_2261_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_r_2275_; 
v_r_2275_ = lean_ctor_get(v_impl_2171_, 4);
lean_inc(v_r_2275_);
if (lean_obj_tag(v_r_2275_) == 0)
{
lean_object* v_k_2276_; lean_object* v_v_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2300_; 
v_k_2276_ = lean_ctor_get(v_impl_2171_, 1);
v_v_2277_ = lean_ctor_get(v_impl_2171_, 2);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; lean_object* v_unused_2302_; lean_object* v_unused_2303_; 
v_unused_2301_ = lean_ctor_get(v_impl_2171_, 4);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2303_);
v___x_2279_ = v_impl_2171_;
v_isShared_2280_ = v_isSharedCheck_2300_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_v_2277_);
lean_inc(v_k_2276_);
lean_dec(v_impl_2171_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2300_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2296_; 
v_k_2281_ = lean_ctor_get(v_r_2275_, 1);
v_v_2282_ = lean_ctor_get(v_r_2275_, 2);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_r_2275_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; 
v_unused_2297_ = lean_ctor_get(v_r_2275_, 4);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_r_2275_, 3);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_r_2275_, 0);
lean_dec(v_unused_2299_);
v___x_2284_ = v_r_2275_;
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_v_2282_);
lean_inc(v_k_2281_);
lean_dec(v_r_2275_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_unsigned_to_nat(3u);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v_l_2258_);
lean_ctor_set(v___x_2284_, 3, v_l_2258_);
lean_ctor_set(v___x_2284_, 2, v_v_2277_);
lean_ctor_set(v___x_2284_, 1, v_k_2276_);
lean_ctor_set(v___x_2284_, 0, v___x_2172_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_k_2276_);
lean_ctor_set(v_reuseFailAlloc_2295_, 2, v_v_2277_);
lean_ctor_set(v_reuseFailAlloc_2295_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2295_, 4, v_l_2258_);
v___x_2288_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 4, v_l_2258_);
lean_ctor_set(v___x_2279_, 2, v_v_2025_);
lean_ctor_set(v___x_2279_, 1, v_k_2024_);
lean_ctor_set(v___x_2279_, 0, v___x_2172_);
v___x_2290_ = v___x_2279_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_l_2258_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2290_);
lean_ctor_set(v___x_2029_, 3, v___x_2288_);
lean_ctor_set(v___x_2029_, 2, v_v_2282_);
lean_ctor_set(v___x_2029_, 1, v_k_2281_);
lean_ctor_set(v___x_2029_, 0, v___x_2286_);
v___x_2292_ = v___x_2029_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_2281_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_2282_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_unsigned_to_nat(2u);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_r_2275_);
lean_ctor_set(v___x_2029_, 3, v_impl_2171_);
lean_ctor_set(v___x_2029_, 0, v___x_2304_);
v___x_2306_ = v___x_2029_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_impl_2171_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2275_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v_k_2020_);
lean_ctor_set(v___x_2310_, 2, v_v_2021_);
lean_ctor_set(v___x_2310_, 3, v_t_2022_);
lean_ctor_set(v___x_2310_, 4, v_t_2022_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2311_, lean_object* v_v_2312_, lean_object* v_x_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_a_2322_; lean_object* v_optionsPerPos_2323_; lean_object* v_currNamespace_2324_; lean_object* v_openDecls_2325_; uint8_t v_inPattern_2326_; lean_object* v_subExpr_2327_; lean_object* v_depth_2328_; lean_object* v_lctxInitIndices_2329_; lean_object* v___y_2331_; lean_object* v___x_2336_; 
v___x_2321_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2314_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v_optionsPerPos_2323_ = lean_ctor_get(v_a_2314_, 0);
v_currNamespace_2324_ = lean_ctor_get(v_a_2314_, 1);
v_openDecls_2325_ = lean_ctor_get(v_a_2314_, 2);
v_inPattern_2326_ = lean_ctor_get_uint8(v_a_2314_, sizeof(void*)*6);
v_subExpr_2327_ = lean_ctor_get(v_a_2314_, 3);
v_depth_2328_ = lean_ctor_get(v_a_2314_, 4);
v_lctxInitIndices_2329_ = lean_ctor_get(v_a_2314_, 5);
v___x_2336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2323_, v_a_2322_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Options_empty;
v___y_2331_ = v___x_2337_;
goto v___jp_2330_;
}
else
{
lean_object* v_val_2338_; 
v_val_2338_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2338_);
lean_dec_ref_known(v___x_2336_, 1);
v___y_2331_ = v_val_2338_;
goto v___jp_2330_;
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2331_, v_k_2311_, v_v_2312_);
lean_inc(v_optionsPerPos_2323_);
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2322_, v___x_2332_, v_optionsPerPos_2323_);
lean_inc(v_lctxInitIndices_2329_);
lean_inc(v_depth_2328_);
lean_inc_ref(v_subExpr_2327_);
lean_inc(v_openDecls_2325_);
lean_inc(v_currNamespace_2324_);
v___x_2334_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v_currNamespace_2324_);
lean_ctor_set(v___x_2334_, 2, v_openDecls_2325_);
lean_ctor_set(v___x_2334_, 3, v_subExpr_2327_);
lean_ctor_set(v___x_2334_, 4, v_depth_2328_);
lean_ctor_set(v___x_2334_, 5, v_lctxInitIndices_2329_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*6, v_inPattern_2326_);
lean_inc(v_a_2319_);
lean_inc_ref(v_a_2318_);
lean_inc(v_a_2317_);
lean_inc_ref(v_a_2316_);
lean_inc(v_a_2315_);
v___x_2335_ = lean_apply_7(v_x_2313_, v___x_2334_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, lean_box(0));
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2339_, lean_object* v_v_2340_, lean_object* v_x_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2339_, v_v_2340_, v_x_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2350_, lean_object* v_k_2351_, lean_object* v_v_2352_, lean_object* v_x_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2351_, v_v_2352_, v_x_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2362_, lean_object* v_k_2363_, lean_object* v_v_2364_, lean_object* v_x_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2362_, v_k_2363_, v_v_2364_, v_x_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2374_, lean_object* v_k_2375_, lean_object* v_v_2376_, lean_object* v_t_2377_, lean_object* v_hl_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2375_, v_v_2376_, v_t_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2380_, lean_object* v_stx_2381_){
_start:
{
uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = 0;
lean_inc(v_pos_2380_);
v___x_2383_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2383_, 0, v_pos_2380_);
lean_ctor_set(v___x_2383_, 1, v_pos_2380_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*2, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_setInfo(v___x_2383_, v_stx_2381_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2397_; 
v___x_2388_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2386_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2389_, v_stx_2385_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2398_, v_a_2399_);
lean_dec_ref(v_a_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2402_, v_a_2403_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2422_, lean_object* v_e_2423_, uint8_t v_isBinder_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_lctx_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_lctx_2427_ = lean_ctor_get(v_a_2425_, 2);
v___x_2428_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v_stx_2422_);
v___x_2430_ = lean_box(0);
v___x_2431_ = 0;
lean_inc_ref(v_lctx_2427_);
v___x_2432_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2432_, 0, v___x_2429_);
lean_ctor_set(v___x_2432_, 1, v_lctx_2427_);
lean_ctor_set(v___x_2432_, 2, v___x_2430_);
lean_ctor_set(v___x_2432_, 3, v_e_2423_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*4, v_isBinder_2424_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*4 + 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2434_, lean_object* v_e_2435_, lean_object* v_isBinder_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_isBinder_boxed_2439_; lean_object* v_res_2440_; 
v_isBinder_boxed_2439_ = lean_unbox(v_isBinder_2436_);
v_res_2440_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2434_, v_e_2435_, v_isBinder_boxed_2439_, v_a_2437_);
lean_dec_ref(v_a_2437_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2441_, lean_object* v_e_2442_, uint8_t v_isBinder_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2441_, v_e_2442_, v_isBinder_2443_, v_a_2446_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2452_, lean_object* v_e_2453_, lean_object* v_isBinder_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
uint8_t v_isBinder_boxed_2462_; lean_object* v_res_2463_; 
v_isBinder_boxed_2462_ = lean_unbox(v_isBinder_2454_);
v_res_2463_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2452_, v_e_2453_, v_isBinder_boxed_2462_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2464_, lean_object* v_stx_2465_, lean_object* v_e_2466_, uint8_t v_isBinder_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2494_; 
v___x_2471_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2465_, v_e_2466_, v_isBinder_2467_, v_a_2469_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2494_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2494_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v_steps_2477_; lean_object* v_infos_2478_; lean_object* v_holeIter_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2493_; 
v___x_2476_ = lean_st_ref_take(v_a_2468_);
v_steps_2477_ = lean_ctor_get(v___x_2476_, 0);
v_infos_2478_ = lean_ctor_get(v___x_2476_, 1);
v_holeIter_2479_ = lean_ctor_get(v___x_2476_, 2);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2481_ = v___x_2476_;
v_isShared_2482_ = v_isSharedCheck_2493_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_holeIter_2479_);
lean_inc(v_infos_2478_);
lean_inc(v_steps_2477_);
lean_dec(v___x_2476_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2493_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2472_);
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2464_, v___x_2483_, v_infos_2478_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2484_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_steps_2477_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_holeIter_2479_);
v___x_2486_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_st_ref_set(v_a_2468_, v___x_2486_);
v___x_2488_ = lean_box(0);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2488_);
v___x_2490_ = v___x_2474_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2495_, lean_object* v_stx_2496_, lean_object* v_e_2497_, lean_object* v_isBinder_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
uint8_t v_isBinder_boxed_2502_; lean_object* v_res_2503_; 
v_isBinder_boxed_2502_ = lean_unbox(v_isBinder_2498_);
v_res_2503_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2495_, v_stx_2496_, v_e_2497_, v_isBinder_boxed_2502_, v_a_2499_, v_a_2500_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2504_, lean_object* v_stx_2505_, lean_object* v_e_2506_, uint8_t v_isBinder_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2504_, v_stx_2505_, v_e_2506_, v_isBinder_2507_, v_a_2509_, v_a_2510_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2516_, lean_object* v_stx_2517_, lean_object* v_e_2518_, lean_object* v_isBinder_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
uint8_t v_isBinder_boxed_2527_; lean_object* v_res_2528_; 
v_isBinder_boxed_2527_ = lean_unbox(v_isBinder_2519_);
v_res_2528_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2516_, v_stx_2517_, v_e_2518_, v_isBinder_boxed_2527_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2529_, lean_object* v_fieldName_2530_, lean_object* v_stx_2531_, lean_object* v_val_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_lctx_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_lctx_2535_ = lean_ctor_get(v_a_2533_, 2);
lean_inc_ref(v_lctx_2535_);
v___x_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2536_, 0, v_projName_2529_);
lean_ctor_set(v___x_2536_, 1, v_fieldName_2530_);
lean_ctor_set(v___x_2536_, 2, v_lctx_2535_);
lean_ctor_set(v___x_2536_, 3, v_val_2532_);
lean_ctor_set(v___x_2536_, 4, v_stx_2531_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2538_, lean_object* v_fieldName_2539_, lean_object* v_stx_2540_, lean_object* v_val_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2538_, v_fieldName_2539_, v_stx_2540_, v_val_2541_, v_a_2542_);
lean_dec_ref(v_a_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2545_, lean_object* v_fieldName_2546_, lean_object* v_stx_2547_, lean_object* v_val_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2545_, v_fieldName_2546_, v_stx_2547_, v_val_2548_, v_a_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2557_, lean_object* v_fieldName_2558_, lean_object* v_stx_2559_, lean_object* v_val_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2557_, v_fieldName_2558_, v_stx_2559_, v_val_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2569_, lean_object* v_projName_2570_, lean_object* v_fieldName_2571_, lean_object* v_stx_2572_, lean_object* v_val_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2600_; 
v___x_2577_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2570_, v_fieldName_2571_, v_stx_2572_, v_val_2573_, v_a_2575_);
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2600_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2600_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v_steps_2583_; lean_object* v_infos_2584_; lean_object* v_holeIter_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2599_; 
v___x_2582_ = lean_st_ref_take(v_a_2574_);
v_steps_2583_ = lean_ctor_get(v___x_2582_, 0);
v_infos_2584_ = lean_ctor_get(v___x_2582_, 1);
v_holeIter_2585_ = lean_ctor_get(v___x_2582_, 2);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2587_ = v___x_2582_;
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_holeIter_2585_);
lean_inc(v_infos_2584_);
lean_inc(v_steps_2583_);
lean_dec(v___x_2582_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2589_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_a_2578_);
v___x_2590_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2569_, v___x_2589_, v_infos_2584_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2590_);
v___x_2592_ = v___x_2587_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_steps_2583_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_holeIter_2585_);
v___x_2592_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_st_ref_set(v_a_2574_, v___x_2592_);
v___x_2594_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2594_);
v___x_2596_ = v___x_2580_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2601_, lean_object* v_projName_2602_, lean_object* v_fieldName_2603_, lean_object* v_stx_2604_, lean_object* v_val_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2601_, v_projName_2602_, v_fieldName_2603_, v_stx_2604_, v_val_2605_, v_a_2606_, v_a_2607_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2610_, lean_object* v_projName_2611_, lean_object* v_fieldName_2612_, lean_object* v_stx_2613_, lean_object* v_val_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2610_, v_projName_2611_, v_fieldName_2612_, v_stx_2613_, v_val_2614_, v_a_2616_, v_a_2617_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2623_, lean_object* v_projName_2624_, lean_object* v_fieldName_2625_, lean_object* v_stx_2626_, lean_object* v_val_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2623_, v_projName_2624_, v_fieldName_2625_, v_stx_2626_, v_val_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_val_2636_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2640_, v___y_2641_);
lean_dec_ref(v___y_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2644_, lean_object* v_stx_2645_, lean_object* v_e_2646_, uint8_t v_isBinder_2647_, lean_object* v_location_x3f_2648_, lean_object* v_docString_x3f_2649_, lean_object* v_mkDocString_x3f_2650_, uint8_t v_explicit_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2690_; 
v___x_2655_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2645_, v_e_2646_, v_isBinder_2647_, v_a_2653_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2690_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2690_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___y_2661_; 
if (lean_obj_tag(v_mkDocString_x3f_2650_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2649_) == 0)
{
v___y_2661_ = v_mkDocString_x3f_2650_;
goto v___jp_2660_;
}
else
{
lean_object* v_val_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2689_; 
v_val_2681_ = lean_ctor_get(v_docString_x3f_2649_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_docString_x3f_2649_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2683_ = v_docString_x3f_2649_;
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_val_2681_);
lean_dec(v_docString_x3f_2649_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___f_2685_; lean_object* v___x_2687_; 
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2685_, 0, v_val_2681_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___f_2685_);
v___x_2687_ = v___x_2683_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___f_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
v___y_2661_ = v___x_2687_;
goto v___jp_2660_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2649_);
v___y_2661_ = v_mkDocString_x3f_2650_;
goto v___jp_2660_;
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v_steps_2663_; lean_object* v_infos_2664_; lean_object* v_holeIter_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2680_; 
v___x_2662_ = lean_st_ref_take(v_a_2652_);
v_steps_2663_ = lean_ctor_get(v___x_2662_, 0);
v_infos_2664_ = lean_ctor_get(v___x_2662_, 1);
v_holeIter_2665_ = lean_ctor_get(v___x_2662_, 2);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2667_ = v___x_2662_;
v_isShared_2668_ = v_isSharedCheck_2680_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_holeIter_2665_);
lean_inc(v_infos_2664_);
lean_inc(v_steps_2663_);
lean_dec(v___x_2662_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2680_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2669_, 0, v_a_2656_);
lean_ctor_set(v___x_2669_, 1, v_location_x3f_2648_);
lean_ctor_set(v___x_2669_, 2, v___y_2661_);
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*3, v_explicit_2651_);
v___x_2670_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
v___x_2671_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2644_, v___x_2670_, v_infos_2664_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2671_);
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_steps_2663_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_holeIter_2665_);
v___x_2673_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_st_ref_set(v_a_2652_, v___x_2673_);
v___x_2675_ = lean_box(0);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2675_);
v___x_2677_ = v___x_2658_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2691_, lean_object* v_stx_2692_, lean_object* v_e_2693_, lean_object* v_isBinder_2694_, lean_object* v_location_x3f_2695_, lean_object* v_docString_x3f_2696_, lean_object* v_mkDocString_x3f_2697_, lean_object* v_explicit_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
uint8_t v_isBinder_boxed_2702_; uint8_t v_explicit_boxed_2703_; lean_object* v_res_2704_; 
v_isBinder_boxed_2702_ = lean_unbox(v_isBinder_2694_);
v_explicit_boxed_2703_ = lean_unbox(v_explicit_2698_);
v_res_2704_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2691_, v_stx_2692_, v_e_2693_, v_isBinder_boxed_2702_, v_location_x3f_2695_, v_docString_x3f_2696_, v_mkDocString_x3f_2697_, v_explicit_boxed_2703_, v_a_2699_, v_a_2700_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2705_, lean_object* v_stx_2706_, lean_object* v_e_2707_, uint8_t v_isBinder_2708_, lean_object* v_location_x3f_2709_, lean_object* v_docString_x3f_2710_, lean_object* v_mkDocString_x3f_2711_, uint8_t v_explicit_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2705_, v_stx_2706_, v_e_2707_, v_isBinder_2708_, v_location_x3f_2709_, v_docString_x3f_2710_, v_mkDocString_x3f_2711_, v_explicit_2712_, v_a_2714_, v_a_2715_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2721_, lean_object* v_stx_2722_, lean_object* v_e_2723_, lean_object* v_isBinder_2724_, lean_object* v_location_x3f_2725_, lean_object* v_docString_x3f_2726_, lean_object* v_mkDocString_x3f_2727_, lean_object* v_explicit_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_isBinder_boxed_2736_; uint8_t v_explicit_boxed_2737_; lean_object* v_res_2738_; 
v_isBinder_boxed_2736_ = lean_unbox(v_isBinder_2724_);
v_explicit_boxed_2737_ = lean_unbox(v_explicit_2728_);
v_res_2738_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2721_, v_stx_2722_, v_e_2723_, v_isBinder_boxed_2736_, v_location_x3f_2725_, v_docString_x3f_2726_, v_mkDocString_x3f_2727_, v_explicit_boxed_2737_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2739_, v_a_2740_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v_a_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_n(v_a_2745_, 2);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2740_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2740_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = 0;
v___x_2751_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2747_, v_a_2745_, v_a_2749_, v___x_2750_, v_a_2741_, v_a_2742_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v___x_2751_, 0);
lean_dec(v_unused_2759_);
v___x_2753_ = v___x_2751_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_dec(v___x_2751_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v_a_2745_);
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2745_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2745_);
v_a_2760_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2751_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2751_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
return v_res_2791_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2792_, lean_object* v_t_2793_){
_start:
{
if (lean_obj_tag(v_t_2793_) == 0)
{
lean_object* v_k_2794_; lean_object* v_l_2795_; lean_object* v_r_2796_; uint8_t v___x_2797_; 
v_k_2794_ = lean_ctor_get(v_t_2793_, 1);
v_l_2795_ = lean_ctor_get(v_t_2793_, 3);
v_r_2796_ = lean_ctor_get(v_t_2793_, 4);
v___x_2797_ = lean_nat_dec_lt(v_k_2792_, v_k_2794_);
if (v___x_2797_ == 0)
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_eq(v_k_2792_, v_k_2794_);
if (v___x_2798_ == 0)
{
v_t_2793_ = v_r_2796_;
goto _start;
}
else
{
return v___x_2798_;
}
}
else
{
v_t_2793_ = v_l_2795_;
goto _start;
}
}
else
{
uint8_t v___x_2801_; 
v___x_2801_ = 0;
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2802_, lean_object* v_t_2803_){
_start:
{
uint8_t v_res_2804_; lean_object* v_r_2805_; 
v_res_2804_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2802_, v_t_2803_);
lean_dec(v_t_2803_);
lean_dec(v_k_2802_);
v_r_2805_ = lean_box(v_res_2804_);
return v_r_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Syntax_getInfo_x3f(v_stx_2806_);
if (lean_obj_tag(v___x_2811_) == 1)
{
lean_object* v_val_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2831_; 
v_val_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2831_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_val_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2831_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_val_2812_) == 1)
{
uint8_t v_canonical_2816_; 
v_canonical_2816_ = lean_ctor_get_uint8(v_val_2812_, sizeof(void*)*2);
if (v_canonical_2816_ == 0)
{
lean_object* v_pos_2817_; lean_object* v_endPos_2818_; lean_object* v___x_2819_; uint8_t v___y_2821_; uint8_t v___x_2826_; 
v_pos_2817_ = lean_ctor_get(v_val_2812_, 0);
lean_inc(v_pos_2817_);
v_endPos_2818_ = lean_ctor_get(v_val_2812_, 1);
lean_inc(v_endPos_2818_);
lean_dec_ref_known(v_val_2812_, 2);
v___x_2819_ = lean_st_ref_get(v_a_2808_);
v___x_2826_ = lean_nat_dec_eq(v_pos_2817_, v_endPos_2818_);
lean_dec(v_endPos_2818_);
if (v___x_2826_ == 0)
{
lean_dec(v___x_2819_);
lean_dec(v_pos_2817_);
v___y_2821_ = v___x_2826_;
goto v___jp_2820_;
}
else
{
lean_object* v_infos_2827_; uint8_t v___x_2828_; 
v_infos_2827_ = lean_ctor_get(v___x_2819_, 1);
lean_inc(v_infos_2827_);
lean_dec(v___x_2819_);
v___x_2828_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2817_, v_infos_2827_);
lean_dec(v_infos_2827_);
lean_dec(v_pos_2817_);
v___y_2821_ = v___x_2828_;
goto v___jp_2820_;
}
v___jp_2820_:
{
if (v___y_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_del_object(v___x_2814_);
v___x_2822_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2822_;
}
else
{
lean_object* v___x_2824_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 0);
lean_ctor_set(v___x_2814_, 0, v_stx_2806_);
v___x_2824_ = v___x_2814_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_stx_2806_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v___x_2829_; 
lean_dec_ref_known(v_val_2812_, 2);
lean_del_object(v___x_2814_);
v___x_2829_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2829_;
}
}
else
{
lean_object* v___x_2830_; 
lean_del_object(v___x_2814_);
lean_dec(v_val_2812_);
v___x_2830_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2830_;
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v___x_2811_);
v___x_2832_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
return v_res_2856_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2857_, lean_object* v_k_2858_, lean_object* v_t_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2858_, v_t_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2861_, lean_object* v_k_2862_, lean_object* v_t_2863_){
_start:
{
uint8_t v_res_2864_; lean_object* v_r_2865_; 
v_res_2864_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2861_, v_k_2862_, v_t_2863_);
lean_dec(v_t_2863_);
lean_dec(v_k_2862_);
v_r_2865_ = lean_box(v_res_2864_);
return v_r_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; 
lean_inc(v_a_2872_);
lean_inc_ref(v_a_2871_);
lean_inc(v_a_2870_);
lean_inc_ref(v_a_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v_a_2867_);
v___x_2874_ = lean_apply_7(v_d_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, lean_box(0));
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2875_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2876_;
}
else
{
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2894_; 
lean_inc(v_a_2892_);
lean_inc_ref(v_a_2891_);
lean_inc(v_a_2890_);
lean_inc_ref(v_a_2889_);
lean_inc(v_a_2888_);
lean_inc_ref(v_a_2887_);
v___x_2894_ = lean_apply_7(v_d_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, lean_box(0));
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2895_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2896_;
}
else
{
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
return v_res_2905_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2906_, lean_object* v_suggestion_x27_2907_, lean_object* v_x_2908_){
_start:
{
if (lean_obj_tag(v_x_2908_) == 1)
{
lean_object* v_fvarId_2909_; lean_object* v___x_2910_; 
v_fvarId_2909_ = lean_ctor_get(v_x_2908_, 0);
lean_inc(v_fvarId_2909_);
lean_dec_ref_known(v_x_2908_, 1);
v___x_2910_ = lean_local_ctx_find(v_lctx_2906_, v_fvarId_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = 0;
return v___x_2911_;
}
else
{
lean_object* v_val_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_val_2912_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_val_2912_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2913_ = l_Lean_LocalDecl_userName(v_val_2912_);
lean_dec(v_val_2912_);
v___x_2914_ = lean_name_eq(v___x_2913_, v_suggestion_x27_2907_);
lean_dec(v___x_2913_);
return v___x_2914_;
}
}
else
{
uint8_t v___x_2915_; 
lean_dec_ref(v_x_2908_);
lean_dec_ref(v_lctx_2906_);
v___x_2915_ = 0;
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2916_, lean_object* v_suggestion_x27_2917_, lean_object* v_x_2918_){
_start:
{
uint8_t v_res_2919_; lean_object* v_r_2920_; 
v_res_2919_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2916_, v_suggestion_x27_2917_, v_x_2918_);
lean_dec(v_suggestion_x27_2917_);
v_r_2920_ = lean_box(v_res_2919_);
return v_r_2920_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2921_, lean_object* v_lctx_2922_, lean_object* v_suggestion_x27_2923_){
_start:
{
lean_object* v___f_2924_; lean_object* v___x_2925_; 
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2924_, 0, v_lctx_2922_);
lean_closure_set(v___f_2924_, 1, v_suggestion_x27_2923_);
v___x_2925_ = lean_find_expr(v___f_2924_, v_body_2921_);
lean_dec_ref(v___f_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
uint8_t v___x_2926_; 
v___x_2926_ = 0;
return v___x_2926_;
}
else
{
uint8_t v___x_2927_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = 1;
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2928_, lean_object* v_lctx_2929_, lean_object* v_suggestion_x27_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2928_, v_lctx_2929_, v_suggestion_x27_2930_);
lean_dec_ref(v_body_2928_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_quotContext_2937_; lean_object* v_currMacroScope_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_quotContext_2937_ = lean_ctor_get(v___y_2934_, 10);
lean_inc(v_quotContext_2937_);
v_currMacroScope_2938_ = lean_ctor_get(v___y_2934_, 11);
lean_inc(v_currMacroScope_2938_);
lean_dec_ref(v___y_2934_);
v___x_2939_ = l_Lean_addMacroScope(v_quotContext_2937_, v_snd_2933_, v_currMacroScope_2938_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_2950_, lean_object* v_body_2951_, uint8_t v_preserveName_2952_, lean_object* v_avoid_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; uint8_t v_fst_2993_; lean_object* v_snd_2994_; uint8_t v___x_3000_; 
v___x_3000_ = l_Lean_Name_isAnonymous(v_suggestion_2950_);
if (v___x_3000_ == 0)
{
uint8_t v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = l_Lean_Name_hasMacroScopes(v_suggestion_2950_);
v___x_3002_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2950_);
v_fst_2993_ = v___x_3001_;
v_snd_2994_ = v___x_3002_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_2993_ = v___x_3000_;
v_snd_2994_ = v___x_3003_;
goto v___jp_2992_;
}
v___jp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = l_Lean_LocalContext_getUnusedName(v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
v___jp_2966_:
{
if (v_preserveName_2952_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_dec_ref(v___y_2967_);
v___x_2970_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_2971_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_2970_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2982_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2982_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_unbox(v_a_2972_);
lean_dec(v_a_2972_);
if (v___x_2976_ == 0)
{
lean_del_object(v___x_2974_);
v___y_2962_ = v___y_2968_;
v___y_2963_ = v___y_2969_;
goto v___jp_2961_;
}
else
{
uint8_t v___x_2977_; 
v___x_2977_ = l_Lean_NameSet_contains(v_avoid_2953_, v___y_2969_);
if (v___x_2977_ == 0)
{
uint8_t v___x_2978_; 
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
v___x_2978_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2951_, v___y_2968_, v___y_2969_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2980_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___y_2969_);
v___x_2980_ = v___x_2974_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___y_2969_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
else
{
lean_del_object(v___x_2974_);
v___y_2962_ = v___y_2968_;
v___y_2963_ = v___y_2969_;
goto v___jp_2961_;
}
}
else
{
lean_del_object(v___x_2974_);
v___y_2962_ = v___y_2968_;
v___y_2963_ = v___y_2969_;
goto v___jp_2961_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v___y_2969_);
v_a_2983_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2971_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2971_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v___x_2991_; 
lean_dec(v___y_2969_);
v___x_2991_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_2967_, v_a_2958_, v_a_2959_);
return v___x_2991_;
}
}
v___jp_2992_:
{
lean_object* v_lctx_2995_; uint8_t v___x_2996_; 
v_lctx_2995_ = lean_ctor_get(v_a_2956_, 2);
v___x_2996_ = l_Lean_LocalContext_usesUserName(v_lctx_2995_, v_snd_2994_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_snd_2994_);
return v___x_2997_;
}
else
{
lean_object* v___f_2998_; 
lean_inc(v_snd_2994_);
v___f_2998_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2998_, 0, v_snd_2994_);
if (v_preserveName_2952_ == 0)
{
v___y_2967_ = v___f_2998_;
v___y_2968_ = v_lctx_2995_;
v___y_2969_ = v_snd_2994_;
goto v___jp_2966_;
}
else
{
if (v_fst_2993_ == 0)
{
lean_object* v___x_2999_; 
lean_dec_ref(v___f_2998_);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_snd_2994_);
return v___x_2999_;
}
else
{
v___y_2967_ = v___f_2998_;
v___y_2968_ = v_lctx_2995_;
v___y_2969_ = v_snd_2994_;
goto v___jp_2966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3004_, lean_object* v_body_3005_, lean_object* v_preserveName_3006_, lean_object* v_avoid_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
uint8_t v_preserveName_boxed_3015_; lean_object* v_res_3016_; 
v_preserveName_boxed_3015_ = lean_unbox(v_preserveName_3006_);
v_res_3016_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3004_, v_body_3005_, v_preserveName_boxed_3015_, v_avoid_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_avoid_3007_);
lean_dec_ref(v_body_3005_);
lean_dec(v_suggestion_3004_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; lean_object* v_holeIter_3020_; lean_object* v_curr_3021_; lean_object* v___x_3022_; lean_object* v_steps_3023_; lean_object* v_infos_3024_; lean_object* v_holeIter_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3035_; 
v___x_3019_ = lean_st_ref_get(v___y_3017_);
v_holeIter_3020_ = lean_ctor_get(v___x_3019_, 2);
lean_inc_ref(v_holeIter_3020_);
lean_dec(v___x_3019_);
v_curr_3021_ = lean_ctor_get(v_holeIter_3020_, 0);
lean_inc(v_curr_3021_);
lean_dec_ref(v_holeIter_3020_);
v___x_3022_ = lean_st_ref_take(v___y_3017_);
v_steps_3023_ = lean_ctor_get(v___x_3022_, 0);
v_infos_3024_ = lean_ctor_get(v___x_3022_, 1);
v_holeIter_3025_ = lean_ctor_get(v___x_3022_, 2);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3027_ = v___x_3022_;
v_isShared_3028_ = v_isSharedCheck_3035_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_holeIter_3025_);
lean_inc(v_infos_3024_);
lean_inc(v_steps_3023_);
lean_dec(v___x_3022_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3035_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3025_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 2, v___x_3029_);
v___x_3031_ = v___x_3027_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_steps_3023_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_infos_3024_);
lean_ctor_set(v_reuseFailAlloc_3034_, 2, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_st_ref_set(v___y_3017_, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_curr_3021_);
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3036_);
lean_dec(v___y_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3040_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3055_, lean_object* v_e_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v___x_3064_; lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3064_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3058_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc_n(v_a_3065_, 2);
lean_dec_ref(v___x_3064_);
v___x_3066_ = l_Lean_mkIdent(v_n_3055_);
v___x_3067_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3065_, v___x_3066_);
v___x_3068_ = 0;
lean_inc(v___x_3067_);
v___x_3069_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3065_, v___x_3067_, v_e_3056_, v___x_3068_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3069_, 0);
lean_dec(v_unused_3077_);
v___x_3071_ = v___x_3069_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v___x_3069_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3067_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3067_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___x_3067_);
v_a_3078_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3069_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3069_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3086_, lean_object* v_e_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3086_, v_e_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
lean_inc(v___y_3103_);
lean_inc_ref(v___y_3102_);
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
lean_inc(v___y_3099_);
lean_inc_ref(v___y_3098_);
v___x_3105_ = lean_apply_8(v_d_3096_, v_x_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, lean_box(0));
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v_b_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
lean_inc(v___y_3118_);
lean_inc_ref(v___y_3117_);
v___x_3125_ = lean_apply_8(v_k_3116_, v_b_3119_, v___y_3117_, v___y_3118_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3126_, v___y_3127_, v___y_3128_, v_b_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3136_, uint8_t v_bi_3137_, lean_object* v_type_3138_, lean_object* v_k_3139_, uint8_t v_kind_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___f_3148_; lean_object* v___x_3149_; 
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
v___f_3148_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3148_, 0, v_k_3139_);
lean_closure_set(v___f_3148_, 1, v___y_3141_);
lean_closure_set(v___f_3148_, 2, v___y_3142_);
v___x_3149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3136_, v_bi_3137_, v_type_3138_, v___f_3148_, v_kind_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3149_) == 0)
{
return v___x_3149_;
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3158_, lean_object* v_bi_3159_, lean_object* v_type_3160_, lean_object* v_k_3161_, lean_object* v_kind_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v_bi_boxed_3170_; uint8_t v_kind_boxed_3171_; lean_object* v_res_3172_; 
v_bi_boxed_3170_ = lean_unbox(v_bi_3159_);
v_kind_boxed_3171_ = lean_unbox(v_kind_3162_);
v_res_3172_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3158_, v_bi_boxed_3170_, v_type_3160_, v_k_3161_, v_kind_boxed_3171_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3173_, lean_object* v_childIdx_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_subExpr_3183_; lean_object* v_optionsPerPos_3184_; lean_object* v_currNamespace_3185_; lean_object* v_openDecls_3186_; uint8_t v_inPattern_3187_; lean_object* v_depth_3188_; lean_object* v_lctxInitIndices_3189_; lean_object* v_pos_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_subExpr_3183_ = lean_ctor_get(v___y_3176_, 3);
v_optionsPerPos_3184_ = lean_ctor_get(v___y_3176_, 0);
v_currNamespace_3185_ = lean_ctor_get(v___y_3176_, 1);
v_openDecls_3186_ = lean_ctor_get(v___y_3176_, 2);
v_inPattern_3187_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*6);
v_depth_3188_ = lean_ctor_get(v___y_3176_, 4);
v_lctxInitIndices_3189_ = lean_ctor_get(v___y_3176_, 5);
v_pos_3190_ = lean_ctor_get(v_subExpr_3183_, 1);
v___x_3191_ = l_Lean_SubExpr_Pos_push(v_pos_3190_, v_childIdx_3174_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v_child_3173_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
lean_inc(v_lctxInitIndices_3189_);
lean_inc(v_depth_3188_);
lean_inc(v_openDecls_3186_);
lean_inc(v_currNamespace_3185_);
lean_inc(v_optionsPerPos_3184_);
v___x_3193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3193_, 0, v_optionsPerPos_3184_);
lean_ctor_set(v___x_3193_, 1, v_currNamespace_3185_);
lean_ctor_set(v___x_3193_, 2, v_openDecls_3186_);
lean_ctor_set(v___x_3193_, 3, v___x_3192_);
lean_ctor_set(v___x_3193_, 4, v_depth_3188_);
lean_ctor_set(v___x_3193_, 5, v_lctxInitIndices_3189_);
lean_ctor_set_uint8(v___x_3193_, sizeof(void*)*6, v_inPattern_3187_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
v___x_3194_ = lean_apply_7(v_x_3175_, v___x_3193_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, lean_box(0));
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3195_, lean_object* v_childIdx_3196_, lean_object* v_x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3195_, v_childIdx_3196_, v_x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3206_, lean_object* v_a_3207_, lean_object* v_x_3208_, lean_object* v_fvar_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc_ref(v_fvar_3209_);
v___x_3217_ = lean_apply_8(v_v_3206_, v_fvar_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, lean_box(0));
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = l_Lean_Expr_bindingBody_x21(v_a_3207_);
v___x_3220_ = lean_expr_instantiate1(v___x_3219_, v_fvar_3209_);
lean_dec_ref(v_fvar_3209_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_apply_1(v_x_3208_, v_a_3218_);
v___x_3223_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3220_, v___x_3221_, v___x_3222_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
return v___x_3223_;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v_fvar_3209_);
lean_dec_ref(v_x_3208_);
v_a_3224_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3217_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3217_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3232_, lean_object* v_a_3233_, lean_object* v_x_3234_, lean_object* v_fvar_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3232_, v_a_3233_, v_x_3234_, v_fvar_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v_a_3233_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3244_, lean_object* v_v_3245_, lean_object* v_x_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; lean_object* v_a_3255_; lean_object* v___f_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3254_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3247_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_n(v_a_3255_, 2);
lean_dec_ref(v___x_3254_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3256_, 0, v_v_3245_);
lean_closure_set(v___f_3256_, 1, v_a_3255_);
lean_closure_set(v___f_3256_, 2, v_x_3246_);
v___x_3257_ = l_Lean_Expr_binderInfo(v_a_3255_);
v___x_3258_ = l_Lean_Expr_bindingDomain_x21(v_a_3255_);
lean_dec(v_a_3255_);
v___x_3259_ = 0;
v___x_3260_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3244_, v___x_3257_, v___x_3258_, v___f_3256_, v___x_3259_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3261_, lean_object* v_v_3262_, lean_object* v_x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3261_, v_v_3262_, v_x_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3272_, uint8_t v_preserveName_3273_, lean_object* v_avoid_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v_a_3283_; lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3282_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3275_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref(v___x_3282_);
v___x_3284_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3275_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v___x_3284_);
v___x_3286_ = l_Lean_Expr_bindingName_x21(v_a_3283_);
lean_dec(v_a_3283_);
v___x_3287_ = l_Lean_Expr_bindingBody_x21(v_a_3285_);
lean_dec(v_a_3285_);
v___x_3288_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3286_, v___x_3287_, v_preserveName_3273_, v_avoid_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3286_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_n(v_a_3289_, 2);
lean_dec_ref_known(v___x_3288_, 1);
v___f_3290_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3290_, 0, v_d_3272_);
v___x_3291_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3291_, 0, v_a_3289_);
v___x_3292_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3289_, v___x_3291_, v___f_3290_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3292_;
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec_ref(v_d_3272_);
v_a_3293_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3288_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3288_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3301_, lean_object* v_preserveName_3302_, lean_object* v_avoid_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
uint8_t v_preserveName_boxed_3311_; lean_object* v_res_3312_; 
v_preserveName_boxed_3311_ = lean_unbox(v_preserveName_3302_);
v_res_3312_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3301_, v_preserveName_boxed_3311_, v_avoid_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_avoid_3303_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3313_, lean_object* v_d_3314_, uint8_t v_preserveName_3315_, lean_object* v_avoid_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3314_, v_preserveName_3315_, v_avoid_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_d_3326_, lean_object* v_preserveName_3327_, lean_object* v_avoid_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
uint8_t v_preserveName_boxed_3336_; lean_object* v_res_3337_; 
v_preserveName_boxed_3336_ = lean_unbox(v_preserveName_3327_);
v_res_3337_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3325_, v_d_3326_, v_preserveName_boxed_3336_, v_avoid_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_avoid_3328_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3338_, lean_object* v_child_3339_, lean_object* v_childIdx_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3339_, v_childIdx_3340_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3350_, lean_object* v_child_3351_, lean_object* v_childIdx_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3350_, v_child_3351_, v_childIdx_3352_, v_x_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3362_, lean_object* v_name_3363_, uint8_t v_bi_3364_, lean_object* v_type_3365_, lean_object* v_k_3366_, uint8_t v_kind_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3363_, v_bi_3364_, v_type_3365_, v_k_3366_, v_kind_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3376_, lean_object* v_name_3377_, lean_object* v_bi_3378_, lean_object* v_type_3379_, lean_object* v_k_3380_, lean_object* v_kind_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v_bi_boxed_3389_; uint8_t v_kind_boxed_3390_; lean_object* v_res_3391_; 
v_bi_boxed_3389_ = lean_unbox(v_bi_3378_);
v_kind_boxed_3390_ = lean_unbox(v_kind_3381_);
v_res_3391_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3376_, v_name_3377_, v_bi_boxed_3389_, v_type_3379_, v_k_3380_, v_kind_boxed_3390_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3392_, lean_object* v_00_u03b2_3393_, lean_object* v_n_3394_, lean_object* v_v_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3394_, v_v_3395_, v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3405_, lean_object* v_00_u03b2_3406_, lean_object* v_n_3407_, lean_object* v_v_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3405_, v_00_u03b2_3406_, v_n_3407_, v_v_3408_, v_x_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object* v_x_3418_){
_start:
{
switch(lean_obj_tag(v_x_3418_))
{
case 0:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_unsigned_to_nat(0u);
return v___x_3419_;
}
case 1:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_unsigned_to_nat(1u);
return v___x_3420_;
}
case 2:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_unsigned_to_nat(2u);
return v___x_3421_;
}
default: 
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_unsigned_to_nat(3u);
return v___x_3422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object* v_x_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(v_x_3423_);
lean_dec(v_x_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3425_, lean_object* v_k_3426_){
_start:
{
if (lean_obj_tag(v_t_3425_) == 3)
{
lean_object* v_s_3427_; lean_object* v___x_3428_; 
v_s_3427_ = lean_ctor_get(v_t_3425_, 0);
lean_inc_ref(v_s_3427_);
lean_dec_ref_known(v_t_3425_, 1);
v___x_3428_ = lean_apply_1(v_k_3426_, v_s_3427_);
return v___x_3428_;
}
else
{
lean_dec(v_t_3425_);
return v_k_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3429_, lean_object* v_ctorIdx_3430_, lean_object* v_t_3431_, lean_object* v_h_3432_, lean_object* v_k_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3431_, v_k_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3435_, lean_object* v_ctorIdx_3436_, lean_object* v_t_3437_, lean_object* v_h_3438_, lean_object* v_k_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3435_, v_ctorIdx_3436_, v_t_3437_, v_h_3438_, v_k_3439_);
lean_dec(v_ctorIdx_3436_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3441_, lean_object* v_deep_3442_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3441_, v_deep_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3444_, lean_object* v_t_3445_, lean_object* v_h_3446_, lean_object* v_deep_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3445_, v_deep_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3449_, lean_object* v_proof_3450_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3449_, v_proof_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3452_, lean_object* v_t_3453_, lean_object* v_h_3454_, lean_object* v_proof_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3453_, v_proof_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3457_, lean_object* v_maxSteps_3458_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3457_, v_maxSteps_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3460_, lean_object* v_t_3461_, lean_object* v_h_3462_, lean_object* v_maxSteps_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3461_, v_maxSteps_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3465_, lean_object* v_string_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3465_, v_string_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3468_, lean_object* v_t_3469_, lean_object* v_h_3470_, lean_object* v_string_3471_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3469_, v_string_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3476_){
_start:
{
switch(lean_obj_tag(v_x_3476_))
{
case 0:
{
lean_object* v___x_3477_; 
v___x_3477_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3477_;
}
case 1:
{
lean_object* v___x_3478_; 
v___x_3478_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3478_;
}
case 2:
{
lean_object* v___x_3479_; 
v___x_3479_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3479_;
}
default: 
{
lean_object* v_s_3480_; 
v_s_3480_ = lean_ctor_get(v_x_3476_, 0);
lean_inc_ref(v_s_3480_);
return v_s_3480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3481_);
lean_dec(v_x_3481_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3483_, lean_object* v_stx_3484_, lean_object* v_e_3485_, lean_object* v_reason_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3490_ = 0;
v___x_3491_ = lean_box(0);
v___x_3492_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3486_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
v___x_3494_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3483_, v_stx_3484_, v_e_3485_, v___x_3490_, v___x_3491_, v___x_3493_, v___x_3491_, v___x_3490_, v_a_3487_, v_a_3488_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3495_, lean_object* v_stx_3496_, lean_object* v_e_3497_, lean_object* v_reason_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3495_, v_stx_3496_, v_e_3497_, v_reason_3498_, v_a_3499_, v_a_3500_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec(v_reason_3498_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3503_, lean_object* v_stx_3504_, lean_object* v_e_3505_, lean_object* v_reason_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3503_, v_stx_3504_, v_e_3505_, v_reason_3506_, v_a_3508_, v_a_3509_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3515_, lean_object* v_stx_3516_, lean_object* v_e_3517_, lean_object* v_reason_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3515_, v_stx_3516_, v_e_3517_, v_reason_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_reason_3518_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3527_, lean_object* v_ctx_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_optionsPerPos_3535_; lean_object* v_currNamespace_3536_; lean_object* v_openDecls_3537_; uint8_t v_inPattern_3538_; lean_object* v_subExpr_3539_; lean_object* v_depth_3540_; lean_object* v_lctxInitIndices_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v_optionsPerPos_3535_ = lean_ctor_get(v_ctx_3528_, 0);
v_currNamespace_3536_ = lean_ctor_get(v_ctx_3528_, 1);
v_openDecls_3537_ = lean_ctor_get(v_ctx_3528_, 2);
v_inPattern_3538_ = lean_ctor_get_uint8(v_ctx_3528_, sizeof(void*)*6);
v_subExpr_3539_ = lean_ctor_get(v_ctx_3528_, 3);
v_depth_3540_ = lean_ctor_get(v_ctx_3528_, 4);
v_lctxInitIndices_3541_ = lean_ctor_get(v_ctx_3528_, 5);
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v_depth_3540_, v___x_3542_);
lean_inc(v_lctxInitIndices_3541_);
lean_inc_ref(v_subExpr_3539_);
lean_inc(v_openDecls_3537_);
lean_inc(v_currNamespace_3536_);
lean_inc(v_optionsPerPos_3535_);
v___x_3544_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3544_, 0, v_optionsPerPos_3535_);
lean_ctor_set(v___x_3544_, 1, v_currNamespace_3536_);
lean_ctor_set(v___x_3544_, 2, v_openDecls_3537_);
lean_ctor_set(v___x_3544_, 3, v_subExpr_3539_);
lean_ctor_set(v___x_3544_, 4, v___x_3543_);
lean_ctor_set(v___x_3544_, 5, v_lctxInitIndices_3541_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*6, v_inPattern_3538_);
lean_inc(v_a_3533_);
lean_inc_ref(v_a_3532_);
lean_inc(v_a_3531_);
lean_inc_ref(v_a_3530_);
lean_inc(v_a_3529_);
v___x_3545_ = lean_apply_7(v_act_3527_, v___x_3544_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, lean_box(0));
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3546_, lean_object* v_ctx_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3546_, v_ctx_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_ctx_3547_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3555_, lean_object* v_act_3556_, lean_object* v_ctx_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3556_, v_ctx_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3565_, lean_object* v_act_3566_, lean_object* v_ctx_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3565_, v_act_3566_, v_ctx_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_ctx_3567_);
return v_res_3574_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3575_, lean_object* v_e_3576_){
_start:
{
lean_object* v___y_3578_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = lean_unsigned_to_nat(254u);
v___x_3583_ = lean_nat_dec_le(v___x_3582_, v_threshold_3575_);
if (v___x_3583_ == 0)
{
v___y_3578_ = v_threshold_3575_;
goto v___jp_3577_;
}
else
{
v___y_3578_ = v___x_3582_;
goto v___jp_3577_;
}
v___jp_3577_:
{
uint32_t v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = l_Lean_Expr_approxDepth(v_e_3576_);
v___x_3580_ = lean_uint32_to_nat(v___x_3579_);
v___x_3581_ = lean_nat_dec_le(v___x_3580_, v___y_3578_);
lean_dec(v___x_3580_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3584_, lean_object* v_e_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3584_, v_e_3585_);
lean_dec_ref(v_e_3585_);
lean_dec(v_threshold_3584_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
uint8_t v___x_3598_; 
v___x_3598_ = l_Lean_Expr_isAtomic(v_e_3590_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3600_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3599_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3644_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3644_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3644_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_unbox(v_a_3601_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_del_object(v___x_3603_);
v___x_3606_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3607_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3606_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3631_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3631_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3631_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v_depth_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v_depth_3612_ = lean_ctor_get(v_a_3591_, 4);
v___x_3613_ = lean_nat_sub(v_depth_3612_, v_a_3608_);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = lean_nat_dec_lt(v___x_3614_, v___x_3613_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3618_; 
lean_dec(v___x_3613_);
lean_dec(v_a_3608_);
lean_dec(v_a_3601_);
v___x_3616_ = lean_box(v___x_3615_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3616_);
v___x_3618_ = v___x_3610_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3620_ = lean_unsigned_to_nat(2u);
v___x_3621_ = lean_nat_shiftr(v_a_3608_, v___x_3620_);
lean_dec(v_a_3608_);
v___x_3622_ = lean_nat_sub(v___x_3621_, v___x_3613_);
lean_dec(v___x_3613_);
lean_dec(v___x_3621_);
v___x_3623_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3622_, v_e_3590_);
lean_dec(v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_dec(v_a_3601_);
v___x_3624_ = lean_box(v___x_3615_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3624_);
v___x_3626_ = v___x_3610_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
else
{
lean_object* v___x_3629_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v_a_3601_);
v___x_3629_ = v___x_3610_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3601_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_a_3601_);
v_a_3632_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3607_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3607_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
lean_dec(v_a_3601_);
v___x_3640_ = lean_box(v___x_3598_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3640_);
v___x_3642_ = v___x_3603_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
return v___x_3600_;
}
}
else
{
uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = 0;
v___x_3646_ = lean_box(v___x_3645_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec_ref(v_e_3648_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Lean_Expr_isAtomic(v_e_3659_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3669_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3668_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3720_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3720_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3720_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___y_3675_; uint8_t v___x_3700_; 
v___x_3700_ = lean_unbox(v_a_3670_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; 
lean_del_object(v___x_3672_);
lean_inc_ref(v_e_3659_);
v___x_3701_ = l_Lean_Meta_isProof(v_e_3659_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3701_) == 0)
{
v___y_3675_ = v___x_3701_;
goto v___jp_3674_;
}
else
{
lean_object* v_a_3702_; uint8_t v___y_3704_; uint8_t v___x_3714_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
v___x_3714_ = l_Lean_Exception_isInterrupt(v_a_3702_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
v___x_3715_ = l_Lean_Exception_isRuntime(v_a_3702_);
v___y_3704_ = v___x_3715_;
goto v___jp_3703_;
}
else
{
lean_dec(v_a_3702_);
v___y_3704_ = v___x_3714_;
goto v___jp_3703_;
}
v___jp_3703_:
{
if (v___y_3704_ == 0)
{
lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3712_; 
lean_dec(v_a_3670_);
lean_dec_ref(v_e_3659_);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v___x_3701_, 0);
lean_dec(v_unused_3713_);
v___x_3706_ = v___x_3701_;
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
else
{
lean_dec(v___x_3701_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3708_ = lean_box(v___y_3704_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3708_);
v___x_3710_ = v___x_3706_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
else
{
v___y_3675_ = v___x_3701_;
goto v___jp_3674_;
}
}
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_a_3670_);
lean_dec_ref(v_e_3659_);
v___x_3716_ = lean_box(v___x_3667_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3716_);
v___x_3718_ = v___x_3672_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
v___jp_3674_:
{
if (lean_obj_tag(v___y_3675_) == 0)
{
lean_object* v_a_3676_; uint8_t v___x_3677_; 
v_a_3676_ = lean_ctor_get(v___y_3675_, 0);
v___x_3677_ = lean_unbox(v_a_3676_);
if (v___x_3677_ == 0)
{
lean_dec(v_a_3670_);
lean_dec_ref(v_e_3659_);
return v___y_3675_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_inc(v_a_3676_);
lean_dec_ref_known(v___y_3675_, 1);
v___x_3678_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3679_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3678_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3691_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3682_ = v___x_3679_;
v_isShared_3683_ = v_isSharedCheck_3691_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3679_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3691_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3680_, v_e_3659_);
lean_dec_ref(v_e_3659_);
lean_dec(v_a_3680_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3686_; 
lean_dec(v_a_3670_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v_a_3676_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3676_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
else
{
lean_object* v___x_3689_; 
lean_dec(v_a_3676_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v_a_3670_);
v___x_3689_ = v___x_3682_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3670_);
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
lean_dec(v_a_3676_);
lean_dec(v_a_3670_);
lean_dec_ref(v_e_3659_);
v_a_3692_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3679_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3679_);
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
}
else
{
lean_dec(v_a_3670_);
lean_dec_ref(v_e_3659_);
return v___y_3675_;
}
}
}
}
else
{
lean_dec_ref(v_e_3659_);
return v___x_3669_;
}
}
else
{
uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref(v_e_3659_);
v___x_3721_ = 0;
v___x_3722_ = lean_box(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_ref_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_ref_3747_ = lean_ctor_get(v_a_3745_, 5);
v___x_3748_ = 0;
v___x_3749_ = l_Lean_SourceInfo_fromRef(v_ref_3747_, v___x_3748_);
v___x_3750_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3751_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3749_);
v___x_3752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3749_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = l_Lean_Syntax_node1(v___x_3749_, v___x_3750_, v___x_3752_);
v___x_3754_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3753_, v_a_3742_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc_n(v_a_3755_, 2);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3742_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3742_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3757_, v_a_3755_, v_a_3759_, v_reason_3741_, v_a_3743_, v_a_3744_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; 
v_unused_3768_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3768_);
v___x_3762_ = v___x_3760_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v___x_3760_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v_a_3755_);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3755_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec(v_a_3755_);
v_a_3769_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3760_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3760_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec_ref(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_reason_3777_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3789_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_reason_3793_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 0)
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3810_;
}
else
{
lean_object* v_head_3811_; lean_object* v_tail_3812_; lean_object* v___x_3813_; 
v_head_3811_ = lean_ctor_get(v_x_3802_, 0);
lean_inc(v_head_3811_);
v_tail_3812_ = lean_ctor_get(v_x_3802_, 1);
lean_inc(v_tail_3812_);
lean_dec_ref_known(v_x_3802_, 2);
lean_inc(v___y_3808_);
lean_inc_ref(v___y_3807_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
v___x_3813_ = lean_apply_7(v_head_3811_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, lean_box(0));
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_dec(v_tail_3812_);
return v___x_3813_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3815_; uint8_t v___y_3817_; uint8_t v___x_3821_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
v___x_3815_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3821_ = l_Lean_Exception_isInterrupt(v_a_3814_);
if (v___x_3821_ == 0)
{
uint8_t v___x_3822_; 
lean_inc(v_a_3814_);
v___x_3822_ = l_Lean_Exception_isRuntime(v_a_3814_);
v___y_3817_ = v___x_3822_;
goto v___jp_3816_;
}
else
{
v___y_3817_ = v___x_3821_;
goto v___jp_3816_;
}
v___jp_3816_:
{
if (v___y_3817_ == 0)
{
if (lean_obj_tag(v_a_3814_) == 0)
{
lean_dec_ref_known(v_a_3814_, 2);
lean_dec(v_tail_3812_);
return v___x_3813_;
}
else
{
lean_object* v_id_3818_; uint8_t v___x_3819_; 
v_id_3818_ = lean_ctor_get(v_a_3814_, 0);
lean_inc(v_id_3818_);
lean_dec_ref_known(v_a_3814_, 2);
v___x_3819_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3815_, v_id_3818_);
lean_dec(v_id_3818_);
if (v___x_3819_ == 0)
{
lean_dec(v_tail_3812_);
return v___x_3813_;
}
else
{
lean_dec_ref_known(v___x_3813_, 1);
v_x_3802_ = v_tail_3812_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3814_);
lean_dec(v_tail_3812_);
return v___x_3813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; uint8_t v___y_3844_; lean_object* v___y_3852_; 
if (lean_obj_tag(v_x_3832_) == 0)
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; lean_object* v_env_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3858_ = lean_st_ref_get(v_a_3838_);
v_env_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc_ref(v_env_3859_);
lean_dec(v___x_3858_);
v___x_3860_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3861_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3860_, v_env_3859_, v_x_3832_);
v___x_3862_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3861_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___x_3864_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3863_, v_a_3833_, v_a_3834_, v_a_3835_);
v___y_3852_ = v___x_3864_;
goto v___jp_3851_;
}
else
{
v___y_3852_ = v___x_3862_;
goto v___jp_3851_;
}
}
v___jp_3840_:
{
if (v___y_3844_ == 0)
{
if (lean_obj_tag(v___y_3842_) == 0)
{
lean_dec_ref_known(v___y_3842_, 2);
lean_dec(v_x_3832_);
return v___y_3841_;
}
else
{
lean_object* v_id_3845_; uint8_t v___x_3846_; 
v_id_3845_ = lean_ctor_get(v___y_3842_, 0);
lean_inc(v_id_3845_);
lean_dec_ref_known(v___y_3842_, 2);
v___x_3846_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3843_, v_id_3845_);
lean_dec(v_id_3845_);
if (v___x_3846_ == 0)
{
lean_dec(v_x_3832_);
return v___y_3841_;
}
else
{
uint8_t v___x_3847_; 
lean_dec_ref(v___y_3841_);
v___x_3847_ = l_Lean_Name_isAtomic(v_x_3832_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_Name_getRoot(v_x_3832_);
lean_dec(v_x_3832_);
v_x_3832_ = v___x_3848_;
goto _start;
}
else
{
lean_object* v___x_3850_; 
lean_dec(v_x_3832_);
v___x_3850_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3850_;
}
}
}
}
else
{
lean_dec_ref(v___y_3842_);
lean_dec(v_x_3832_);
return v___y_3841_;
}
}
v___jp_3851_:
{
if (lean_obj_tag(v___y_3852_) == 0)
{
lean_dec(v_x_3832_);
return v___y_3852_;
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_a_3853_ = lean_ctor_get(v___y_3852_, 0);
lean_inc(v_a_3853_);
v___x_3854_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3855_ = l_Lean_Exception_isInterrupt(v_a_3853_);
if (v___x_3855_ == 0)
{
uint8_t v___x_3856_; 
lean_inc(v_a_3853_);
v___x_3856_ = l_Lean_Exception_isRuntime(v_a_3853_);
v___y_3841_ = v___y_3852_;
v___y_3842_ = v_a_3853_;
v___y_3843_ = v___x_3854_;
v___y_3844_ = v___x_3856_;
goto v___jp_3840_;
}
else
{
v___y_3841_ = v___y_3852_;
v___y_3842_ = v_a_3853_;
v___y_3843_ = v___x_3854_;
v___y_3844_ = v___x_3855_;
goto v___jp_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; lean_object* v_env_3881_; lean_object* v___x_3882_; lean_object* v_mctx_3883_; lean_object* v_lctx_3884_; lean_object* v_options_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3880_ = lean_st_ref_get(v___y_3878_);
v_env_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc_ref(v_env_3881_);
lean_dec(v___x_3880_);
v___x_3882_ = lean_st_ref_get(v___y_3876_);
v_mctx_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc_ref(v_mctx_3883_);
lean_dec(v___x_3882_);
v_lctx_3884_ = lean_ctor_get(v___y_3875_, 2);
v_options_3885_ = lean_ctor_get(v___y_3877_, 2);
lean_inc_ref(v_options_3885_);
lean_inc_ref(v_lctx_3884_);
v___x_3886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3886_, 0, v_env_3881_);
lean_ctor_set(v___x_3886_, 1, v_mctx_3883_);
lean_ctor_set(v___x_3886_, 2, v_lctx_3884_);
lean_ctor_set(v___x_3886_, 3, v_options_3885_);
v___x_3887_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v_msgData_3874_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_ref_3902_; lean_object* v___x_3903_; lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3912_; 
v_ref_3902_ = lean_ctor_get(v___y_3899_, 5);
v___x_3903_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_inc(v_ref_3902_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_ref_3902_);
lean_ctor_set(v___x_3908_, 1, v_a_3904_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set_tag(v___x_3906_, 1);
lean_ctor_set(v___x_3906_, 0, v___x_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3919_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3922_ = l_Lean_stringToMessageData(v___x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v___x_3931_; 
lean_inc(v_a_3923_);
v___x_3931_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_dec(v_a_3923_);
return v___x_3931_;
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3933_; uint8_t v___y_3935_; uint8_t v___x_3951_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
v___x_3933_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3951_ = l_Lean_Exception_isInterrupt(v_a_3932_);
if (v___x_3951_ == 0)
{
uint8_t v___x_3952_; 
lean_inc(v_a_3932_);
v___x_3952_ = l_Lean_Exception_isRuntime(v_a_3932_);
v___y_3935_ = v___x_3952_;
goto v___jp_3934_;
}
else
{
v___y_3935_ = v___x_3951_;
goto v___jp_3934_;
}
v___jp_3934_:
{
if (v___y_3935_ == 0)
{
if (lean_obj_tag(v_a_3932_) == 0)
{
lean_dec_ref_known(v_a_3932_, 2);
lean_dec(v_a_3923_);
return v___x_3931_;
}
else
{
lean_object* v_id_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3949_; 
v_id_3936_ = lean_ctor_get(v_a_3932_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_a_3932_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v_a_3932_, 1);
lean_dec(v_unused_3950_);
v___x_3938_ = v_a_3932_;
v_isShared_3939_ = v_isSharedCheck_3949_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_id_3936_);
lean_dec(v_a_3932_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3949_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
uint8_t v___x_3940_; 
v___x_3940_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3933_, v_id_3936_);
lean_dec(v_id_3936_);
if (v___x_3940_ == 0)
{
lean_del_object(v___x_3938_);
lean_dec(v_a_3923_);
return v___x_3931_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
lean_dec_ref_known(v___x_3931_, 1);
v___x_3941_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_3942_ = l_Lean_MessageData_ofName(v_a_3923_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 7);
lean_ctor_set(v___x_3938_, 1, v___x_3942_);
lean_ctor_set(v___x_3938_, 0, v___x_3941_);
v___x_3944_ = v___x_3938_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_3946_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
return v___x_3947_;
}
}
}
}
}
else
{
lean_dec(v_a_3932_);
lean_dec(v_a_3923_);
return v___x_3931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v_a_3971_; lean_object* v___x_3972_; 
v___x_3970_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3963_);
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
lean_inc(v___y_3968_);
lean_inc_ref(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
v___x_3972_ = lean_infer_type(v_a_3971_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_3975_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_3973_, v___x_3974_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3975_;
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec_ref(v_x_3962_);
v_a_3976_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3972_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3972_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3992_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_4011_ = l_String_toRawSubstring_x27(v___x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_4070_ = l_Lean_Core_checkSystem(v___x_4069_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref_known(v___x_4070_, 1);
v___x_4071_ = lean_st_ref_get(v_a_4063_);
v___x_4072_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4073_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4072_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v_steps_4075_; uint8_t v___x_4076_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v_steps_4075_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_steps_4075_);
lean_dec(v___x_4071_);
v___x_4076_ = lean_nat_dec_le(v_a_4074_, v_steps_4075_);
lean_dec(v_steps_4075_);
lean_dec(v_a_4074_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v_steps_4078_; lean_object* v_infos_4079_; lean_object* v_holeIter_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4251_; 
v___x_4077_ = lean_st_ref_take(v_a_4063_);
v_steps_4078_ = lean_ctor_get(v___x_4077_, 0);
v_infos_4079_ = lean_ctor_get(v___x_4077_, 1);
v_holeIter_4080_ = lean_ctor_get(v___x_4077_, 2);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4082_ = v___x_4077_;
v_isShared_4083_ = v_isSharedCheck_4251_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_holeIter_4080_);
lean_inc(v_infos_4079_);
lean_inc(v_steps_4078_);
lean_dec(v___x_4077_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4251_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = lean_unsigned_to_nat(1u);
v___x_4085_ = lean_nat_add(v_steps_4078_, v___x_4084_);
lean_dec(v_steps_4078_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4085_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_infos_4079_);
lean_ctor_set(v_reuseFailAlloc_4250_, 2, v_holeIter_4080_);
v___x_4087_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_st_ref_set(v_a_4063_, v___x_4087_);
v___x_4089_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4062_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4090_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; uint8_t v___x_4093_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v___x_4093_ = lean_unbox(v_a_4092_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; 
lean_inc(v_a_4090_);
v___x_4094_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4090_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; uint8_t v___x_4096_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = lean_unbox(v_a_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; 
lean_dec(v_a_4092_);
v___x_4097_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___f_4099_; lean_object* v___x_4100_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4097_, 1);
v___f_4099_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4099_, 0, v_a_4098_);
v___x_4100_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4099_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___y_4103_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
v___x_4149_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4150_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4149_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; uint8_t v___x_4152_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
v___x_4152_ = lean_unbox(v_a_4151_);
lean_dec(v_a_4151_);
if (v___x_4152_ == 0)
{
lean_dec(v_a_4090_);
v___y_4103_ = v___x_4150_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec_ref_known(v___x_4150_, 1);
v___x_4153_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4154_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4153_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; uint8_t v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
v___x_4156_ = lean_unbox(v_a_4155_);
lean_dec(v_a_4155_);
if (v___x_4156_ == 0)
{
lean_dec(v_a_4090_);
v___y_4103_ = v___x_4154_;
goto v___jp_4102_;
}
else
{
uint8_t v___x_4157_; 
v___x_4157_ = l_Lean_Expr_isMData(v_a_4090_);
lean_dec(v_a_4090_);
if (v___x_4157_ == 0)
{
v___y_4103_ = v___x_4154_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_a_4095_);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v___x_4154_, 0);
lean_dec(v_unused_4165_);
v___x_4159_ = v___x_4154_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v___x_4154_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v_a_4101_);
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4101_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
else
{
lean_dec(v_a_4090_);
v___y_4103_ = v___x_4154_;
goto v___jp_4102_;
}
}
}
else
{
lean_dec(v_a_4090_);
v___y_4103_ = v___x_4150_;
goto v___jp_4102_;
}
v___jp_4102_:
{
if (lean_obj_tag(v___y_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4140_; 
v_a_4104_ = lean_ctor_get(v___y_4103_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___y_4103_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4106_ = v___y_4103_;
v_isShared_4107_ = v_isSharedCheck_4140_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___y_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4140_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_unbox(v_a_4104_);
lean_dec(v_a_4104_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4110_; 
lean_dec(v_a_4095_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v_a_4101_);
v___x_4110_ = v___x_4106_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4101_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_del_object(v___x_4106_);
v___x_4112_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4113_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4112_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v_ref_4115_; lean_object* v_quotContext_4116_; lean_object* v_currMacroScope_4117_; uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
v_ref_4115_ = lean_ctor_get(v_a_4066_, 5);
v_quotContext_4116_ = lean_ctor_get(v_a_4066_, 10);
v_currMacroScope_4117_ = lean_ctor_get(v_a_4066_, 11);
v___x_4118_ = lean_unbox(v_a_4095_);
lean_dec(v_a_4095_);
v___x_4119_ = l_Lean_SourceInfo_fromRef(v_ref_4115_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4121_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4122_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4119_, 7);
v___x_4123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4119_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4125_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4126_ = lean_box(0);
lean_inc(v_currMacroScope_4117_);
lean_inc(v_quotContext_4116_);
v___x_4127_ = l_Lean_addMacroScope(v_quotContext_4116_, v___x_4126_, v_currMacroScope_4117_);
v___x_4128_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4119_);
lean_ctor_set(v___x_4129_, 1, v___x_4125_);
lean_ctor_set(v___x_4129_, 2, v___x_4127_);
lean_ctor_set(v___x_4129_, 3, v___x_4128_);
v___x_4130_ = l_Lean_Syntax_node1(v___x_4119_, v___x_4124_, v___x_4129_);
v___x_4131_ = l_Lean_Syntax_node2(v___x_4119_, v___x_4121_, v___x_4123_, v___x_4130_);
v___x_4132_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4119_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_4135_ = l_Lean_Syntax_node1(v___x_4119_, v___x_4134_, v_a_4114_);
v___x_4136_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4119_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = l_Lean_Syntax_node5(v___x_4119_, v___x_4120_, v___x_4131_, v_a_4101_, v___x_4133_, v___x_4135_, v___x_4137_);
v___x_4139_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4138_, v_a_4062_);
return v___x_4139_;
}
else
{
lean_dec(v_a_4101_);
lean_dec(v_a_4095_);
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec(v_a_4101_);
lean_dec(v_a_4095_);
v_a_4141_ = lean_ctor_get(v___y_4103_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___y_4103_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___y_4103_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___y_4103_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
else
{
lean_dec(v_a_4095_);
lean_dec(v_a_4090_);
return v___x_4100_;
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_a_4095_);
lean_dec(v_a_4090_);
v_a_4166_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4097_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4097_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec(v_a_4095_);
lean_dec(v_a_4090_);
v___x_4174_ = lean_box(1);
v___x_4175_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4174_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4066_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___x_4177_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4178_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4177_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4215_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4181_ = v___x_4178_;
v_isShared_4182_ = v_isSharedCheck_4215_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4178_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4215_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_unbox(v_a_4179_);
lean_dec(v_a_4179_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4185_; 
lean_dec(v_a_4092_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v_a_4176_);
v___x_4185_ = v___x_4181_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4176_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_del_object(v___x_4181_);
v___x_4187_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4188_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4187_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v_ref_4190_; lean_object* v_quotContext_4191_; lean_object* v_currMacroScope_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v_ref_4190_ = lean_ctor_get(v_a_4066_, 5);
v_quotContext_4191_ = lean_ctor_get(v_a_4066_, 10);
v_currMacroScope_4192_ = lean_ctor_get(v_a_4066_, 11);
v___x_4193_ = lean_unbox(v_a_4092_);
lean_dec(v_a_4092_);
v___x_4194_ = l_Lean_SourceInfo_fromRef(v_ref_4190_, v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4196_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4197_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4194_, 7);
v___x_4198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4194_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4200_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4201_ = lean_box(0);
lean_inc(v_currMacroScope_4192_);
lean_inc(v_quotContext_4191_);
v___x_4202_ = l_Lean_addMacroScope(v_quotContext_4191_, v___x_4201_, v_currMacroScope_4192_);
v___x_4203_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4194_);
lean_ctor_set(v___x_4204_, 1, v___x_4200_);
lean_ctor_set(v___x_4204_, 2, v___x_4202_);
lean_ctor_set(v___x_4204_, 3, v___x_4203_);
v___x_4205_ = l_Lean_Syntax_node1(v___x_4194_, v___x_4199_, v___x_4204_);
v___x_4206_ = l_Lean_Syntax_node2(v___x_4194_, v___x_4196_, v___x_4198_, v___x_4205_);
v___x_4207_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4194_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_4210_ = l_Lean_Syntax_node1(v___x_4194_, v___x_4209_, v_a_4189_);
v___x_4211_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4194_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___x_4213_ = l_Lean_Syntax_node5(v___x_4194_, v___x_4195_, v___x_4206_, v_a_4176_, v___x_4208_, v___x_4210_, v___x_4212_);
v___x_4214_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4213_, v_a_4062_);
return v___x_4214_;
}
else
{
lean_dec(v_a_4176_);
lean_dec(v_a_4092_);
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_a_4176_);
lean_dec(v_a_4092_);
v_a_4216_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4178_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4178_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
else
{
lean_dec(v_a_4092_);
return v___x_4175_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_a_4092_);
lean_dec(v_a_4090_);
v_a_4224_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4094_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4094_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec(v_a_4092_);
lean_dec(v_a_4090_);
v___x_4232_ = lean_box(0);
v___x_4233_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4232_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4066_);
return v___x_4233_;
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_a_4090_);
v_a_4234_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4091_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4091_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4242_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4089_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4089_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_box(2);
v___x_4253_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4252_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4066_);
return v___x_4253_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec(v___x_4071_);
v_a_4254_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4073_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4073_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4070_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4070_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4270_, lean_object* v_msg_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4278_, lean_object* v_msg_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4278_, v_msg_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4286_, lean_object* v_x_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4296_, v_x_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4307_, lean_object* v_prec_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4317_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4316_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4330_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4320_ = v___x_4317_;
v_isShared_4321_ = v_isSharedCheck_4330_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4317_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4330_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v_mctx_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4322_ = lean_st_ref_get(v_a_4312_);
v_mctx_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc_ref(v_mctx_4323_);
lean_dec(v___x_4322_);
v___x_4324_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4324_, 0, v_mctx_4323_);
v___x_4325_ = lean_unbox(v_a_4318_);
lean_dec(v_a_4318_);
v___x_4326_ = l_Lean_Level_quote(v_l_4307_, v_prec_4308_, v___x_4325_, v___x_4324_);
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 0, v___x_4326_);
v___x_4328_ = v___x_4320_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_l_4307_);
v_a_4331_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4317_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4317_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4339_, lean_object* v_prec_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4339_, v_prec_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_prec_4340_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4349_, lean_object* v_stx_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4350_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_box(0);
v___x_4357_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4355_, v___x_4356_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc_n(v_a_4358_, 2);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = 0;
v___x_4360_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_a_4358_, v___x_4359_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; 
v_unused_4368_ = lean_ctor_get(v___x_4360_, 0);
lean_dec(v_unused_4368_);
v___x_4362_ = v___x_4360_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_dec(v___x_4360_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v_a_4358_);
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4358_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec(v_a_4358_);
v_a_4369_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4360_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4360_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
else
{
return v___x_4357_;
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v_a_4377_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4354_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4354_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4385_, lean_object* v_stx_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
uint8_t v_x_409__boxed_4390_; lean_object* v_res_4391_; 
v_x_409__boxed_4390_ = lean_unbox(v_x_4385_);
v_res_4391_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_409__boxed_4390_, v_stx_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4417_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4418_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4416_, v___x_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4424_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4425_ = l_Lean_addBuiltinDocString(v___x_4423_, v___x_4424_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4455_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4456_ = l_Lean_addBuiltinDeclarationRanges(v___x_4454_, v___x_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; lean_object* v_mctx_4463_; lean_object* v___x_4464_; lean_object* v_fst_4465_; lean_object* v_snd_4466_; lean_object* v___x_4467_; lean_object* v_cache_4468_; lean_object* v_zetaDeltaFVarIds_4469_; lean_object* v_postponed_4470_; lean_object* v_diag_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4480_; 
v___x_4462_ = lean_st_ref_get(v___y_4460_);
v_mctx_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc_ref(v_mctx_4463_);
lean_dec(v___x_4462_);
v___x_4464_ = lean_instantiate_level_mvars(v_mctx_4463_, v_l_4459_);
v_fst_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_fst_4465_);
v_snd_4466_ = lean_ctor_get(v___x_4464_, 1);
lean_inc(v_snd_4466_);
lean_dec_ref(v___x_4464_);
v___x_4467_ = lean_st_ref_take(v___y_4460_);
v_cache_4468_ = lean_ctor_get(v___x_4467_, 1);
v_zetaDeltaFVarIds_4469_ = lean_ctor_get(v___x_4467_, 2);
v_postponed_4470_ = lean_ctor_get(v___x_4467_, 3);
v_diag_4471_ = lean_ctor_get(v___x_4467_, 4);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; 
v_unused_4481_ = lean_ctor_get(v___x_4467_, 0);
lean_dec(v_unused_4481_);
v___x_4473_ = v___x_4467_;
v_isShared_4474_ = v_isSharedCheck_4480_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_diag_4471_);
lean_inc(v_postponed_4470_);
lean_inc(v_zetaDeltaFVarIds_4469_);
lean_inc(v_cache_4468_);
lean_dec(v___x_4467_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4480_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v_fst_4465_);
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_fst_4465_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_cache_4468_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_zetaDeltaFVarIds_4469_);
lean_ctor_set(v_reuseFailAlloc_4479_, 3, v_postponed_4470_);
lean_ctor_set(v_reuseFailAlloc_4479_, 4, v_diag_4471_);
v___x_4476_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = lean_st_ref_set(v___y_4460_, v___x_4476_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v_snd_4466_);
return v___x_4478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4482_, v___y_4483_);
lean_dec(v___y_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4486_, v___y_4488_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4500_, lean_object* v_prec_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_l_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v_options_4518_; uint8_t v___x_4519_; 
v_options_4518_ = lean_ctor_get(v_a_4504_, 2);
v___x_4519_ = l_Lean_getPPInstantiateMVars(v_options_4518_);
if (v___x_4519_ == 0)
{
v_l_4508_ = v_l_4500_;
v___y_4509_ = v_a_4503_;
v___y_4510_ = v_a_4504_;
goto v___jp_4507_;
}
else
{
lean_object* v___x_4520_; lean_object* v_a_4521_; 
v___x_4520_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4500_, v_a_4503_);
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref(v___x_4520_);
v_l_4508_ = v_a_4521_;
v___y_4509_ = v_a_4503_;
v___y_4510_ = v_a_4504_;
goto v___jp_4507_;
}
v___jp_4507_:
{
lean_object* v___x_4511_; lean_object* v_options_4512_; lean_object* v_mctx_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4511_ = lean_st_ref_get(v___y_4509_);
v_options_4512_ = lean_ctor_get(v___y_4510_, 2);
v_mctx_4513_ = lean_ctor_get(v___x_4511_, 0);
lean_inc_ref(v_mctx_4513_);
lean_dec(v___x_4511_);
v___x_4514_ = l_Lean_getPPMVarsLevels(v_options_4512_);
v___x_4515_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4515_, 0, v_mctx_4513_);
v___x_4516_ = l_Lean_Level_quote(v_l_4508_, v_prec_4501_, v___x_4514_, v___x_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4522_, lean_object* v_prec_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_PrettyPrinter_delabLevel(v_l_4522_, v_prec_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_prec_4523_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___f_4537_; lean_object* v___x_8584__overap_4538_; lean_object* v___x_4539_; 
v___f_4537_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8584__overap_4538_ = lean_panic_fn_borrowed(v___f_4537_, v_msg_4531_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc_ref(v___y_4532_);
v___x_4539_ = lean_apply_5(v___x_8584__overap_4538_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, lean_box(0));
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4547_, lean_object* v_msg_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4555_, lean_object* v_msg_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4555_, v_msg_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
return v_res_4562_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4563_, lean_object* v_opt_4564_){
_start:
{
lean_object* v_name_4565_; lean_object* v_defValue_4566_; lean_object* v_map_4567_; lean_object* v___x_4568_; 
v_name_4565_ = lean_ctor_get(v_opt_4564_, 0);
v_defValue_4566_ = lean_ctor_get(v_opt_4564_, 1);
v_map_4567_ = lean_ctor_get(v_opts_4563_, 0);
v___x_4568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4567_, v_name_4565_);
if (lean_obj_tag(v___x_4568_) == 0)
{
uint8_t v___x_4569_; 
v___x_4569_ = lean_unbox(v_defValue_4566_);
return v___x_4569_;
}
else
{
lean_object* v_val_4570_; 
v_val_4570_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_val_4570_);
lean_dec_ref_known(v___x_4568_, 1);
if (lean_obj_tag(v_val_4570_) == 1)
{
uint8_t v_v_4571_; 
v_v_4571_ = lean_ctor_get_uint8(v_val_4570_, 0);
lean_dec_ref_known(v_val_4570_, 0);
return v_v_4571_;
}
else
{
uint8_t v___x_4572_; 
lean_dec(v_val_4570_);
v___x_4572_ = lean_unbox(v_defValue_4566_);
return v___x_4572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4573_, lean_object* v_opt_4574_){
_start:
{
uint8_t v_res_4575_; lean_object* v_r_4576_; 
v_res_4575_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4573_, v_opt_4574_);
lean_dec_ref(v_opt_4574_);
lean_dec_ref(v_opts_4573_);
v_r_4576_ = lean_box(v_res_4575_);
return v_r_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_opts_4577_, lean_object* v_opt_4578_){
_start:
{
lean_object* v_name_4579_; lean_object* v_defValue_4580_; lean_object* v_map_4581_; lean_object* v___x_4582_; 
v_name_4579_ = lean_ctor_get(v_opt_4578_, 0);
v_defValue_4580_ = lean_ctor_get(v_opt_4578_, 1);
v_map_4581_ = lean_ctor_get(v_opts_4577_, 0);
v___x_4582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4581_, v_name_4579_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_inc(v_defValue_4580_);
return v_defValue_4580_;
}
else
{
lean_object* v_val_4583_; 
v_val_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_val_4583_);
lean_dec_ref_known(v___x_4582_, 1);
if (lean_obj_tag(v_val_4583_) == 3)
{
lean_object* v_v_4584_; 
v_v_4584_ = lean_ctor_get(v_val_4583_, 0);
lean_inc(v_v_4584_);
lean_dec_ref_known(v_val_4583_, 1);
return v_v_4584_;
}
else
{
lean_dec(v_val_4583_);
lean_inc(v_defValue_4580_);
return v_defValue_4580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_opts_4585_, lean_object* v_opt_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v_opts_4585_, v_opt_4586_);
lean_dec_ref(v_opt_4586_);
lean_dec_ref(v_opts_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(lean_object* v_e_4588_, lean_object* v___y_4589_){
_start:
{
uint8_t v___x_4591_; 
v___x_4591_ = l_Lean_Expr_hasMVar(v_e_4588_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_e_4588_);
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; lean_object* v_mctx_4594_; lean_object* v___x_4595_; lean_object* v_fst_4596_; lean_object* v_snd_4597_; lean_object* v___x_4598_; lean_object* v_cache_4599_; lean_object* v_zetaDeltaFVarIds_4600_; lean_object* v_postponed_4601_; lean_object* v_diag_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4611_; 
v___x_4593_ = lean_st_ref_get(v___y_4589_);
v_mctx_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc_ref(v_mctx_4594_);
lean_dec(v___x_4593_);
v___x_4595_ = l_Lean_instantiateMVarsCore(v_mctx_4594_, v_e_4588_);
v_fst_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_fst_4596_);
v_snd_4597_ = lean_ctor_get(v___x_4595_, 1);
lean_inc(v_snd_4597_);
lean_dec_ref(v___x_4595_);
v___x_4598_ = lean_st_ref_take(v___y_4589_);
v_cache_4599_ = lean_ctor_get(v___x_4598_, 1);
v_zetaDeltaFVarIds_4600_ = lean_ctor_get(v___x_4598_, 2);
v_postponed_4601_ = lean_ctor_get(v___x_4598_, 3);
v_diag_4602_ = lean_ctor_get(v___x_4598_, 4);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4611_ == 0)
{
lean_object* v_unused_4612_; 
v_unused_4612_ = lean_ctor_get(v___x_4598_, 0);
lean_dec(v_unused_4612_);
v___x_4604_ = v___x_4598_;
v_isShared_4605_ = v_isSharedCheck_4611_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_diag_4602_);
lean_inc(v_postponed_4601_);
lean_inc(v_zetaDeltaFVarIds_4600_);
lean_inc(v_cache_4599_);
lean_dec(v___x_4598_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4611_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 0, v_snd_4597_);
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_snd_4597_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_cache_4599_);
lean_ctor_set(v_reuseFailAlloc_4610_, 2, v_zetaDeltaFVarIds_4600_);
lean_ctor_set(v_reuseFailAlloc_4610_, 3, v_postponed_4601_);
lean_ctor_set(v_reuseFailAlloc_4610_, 4, v_diag_4602_);
v___x_4607_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_st_ref_set(v___y_4589_, v___x_4607_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v_fst_4596_);
return v___x_4609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg___boxed(lean_object* v_e_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4613_, v___y_4614_);
lean_dec(v___y_4614_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_e_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4617_, v___y_4619_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_e_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(v_e_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4631_, lean_object* v_opt_4632_){
_start:
{
lean_object* v_name_4633_; lean_object* v_map_4634_; lean_object* v___x_4635_; 
v_name_4633_ = lean_ctor_get(v_opt_4632_, 0);
v_map_4634_ = lean_ctor_get(v_opts_4631_, 0);
v___x_4635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4634_, v_name_4633_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; 
v___x_4636_ = lean_box(0);
return v___x_4636_;
}
else
{
lean_object* v_val_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4647_; 
v_val_4637_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4639_ = v___x_4635_;
v_isShared_4640_ = v_isSharedCheck_4647_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_val_4637_);
lean_dec(v___x_4635_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4647_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
if (lean_obj_tag(v_val_4637_) == 1)
{
uint8_t v_v_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
v_v_4641_ = lean_ctor_get_uint8(v_val_4637_, 0);
lean_dec_ref_known(v_val_4637_, 0);
v___x_4642_ = lean_box(v_v_4641_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4642_);
v___x_4644_ = v___x_4639_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
else
{
lean_object* v___x_4646_; 
lean_del_object(v___x_4639_);
lean_dec(v_val_4637_);
v___x_4646_ = lean_box(0);
return v___x_4646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4648_, lean_object* v_opt_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4648_, v_opt_4649_);
lean_dec_ref(v_opt_4649_);
lean_dec_ref(v_opts_4648_);
return v_res_4650_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_x_4651_, lean_object* v_x_4652_){
_start:
{
if (lean_obj_tag(v_x_4651_) == 0)
{
if (lean_obj_tag(v_x_4652_) == 0)
{
uint8_t v___x_4653_; 
v___x_4653_ = 1;
return v___x_4653_;
}
else
{
uint8_t v___x_4654_; 
v___x_4654_ = 0;
return v___x_4654_;
}
}
else
{
if (lean_obj_tag(v_x_4652_) == 0)
{
uint8_t v___x_4655_; 
v___x_4655_ = 0;
return v___x_4655_;
}
else
{
lean_object* v_val_4656_; uint8_t v___x_4657_; 
v_val_4656_ = lean_ctor_get(v_x_4651_, 0);
v___x_4657_ = lean_unbox(v_val_4656_);
if (v___x_4657_ == 0)
{
lean_object* v_val_4658_; uint8_t v___x_4659_; 
v_val_4658_ = lean_ctor_get(v_x_4652_, 0);
v___x_4659_ = lean_unbox(v_val_4658_);
if (v___x_4659_ == 0)
{
uint8_t v___x_4660_; 
v___x_4660_ = 1;
return v___x_4660_;
}
else
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_unbox(v_val_4656_);
return v___x_4661_;
}
}
else
{
lean_object* v_val_4662_; uint8_t v___x_4663_; 
v_val_4662_ = lean_ctor_get(v_x_4652_, 0);
v___x_4663_ = lean_unbox(v_val_4662_);
return v___x_4663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_x_4664_, lean_object* v_x_4665_){
_start:
{
uint8_t v_res_4666_; lean_object* v_r_4667_; 
v_res_4666_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v_x_4664_, v_x_4665_);
lean_dec(v_x_4665_);
lean_dec(v_x_4664_);
v_r_4667_ = lean_box(v_res_4666_);
return v_r_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object* v_o_4668_, lean_object* v_k_4669_, uint8_t v_v_4670_){
_start:
{
lean_object* v_map_4671_; uint8_t v_hasTrace_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4686_; 
v_map_4671_ = lean_ctor_get(v_o_4668_, 0);
v_hasTrace_4672_ = lean_ctor_get_uint8(v_o_4668_, sizeof(void*)*1);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_o_4668_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4674_ = v_o_4668_;
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_map_4671_);
lean_dec(v_o_4668_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4676_, 0, v_v_4670_);
lean_inc(v_k_4669_);
v___x_4677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4669_, v___x_4676_, v_map_4671_);
if (v_hasTrace_4672_ == 0)
{
lean_object* v___x_4678_; uint8_t v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_4679_ = l_Lean_Name_isPrefixOf(v___x_4678_, v_k_4669_);
lean_dec(v_k_4669_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4681_ = v___x_4674_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4677_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_ctor_set_uint8(v___x_4681_, sizeof(void*)*1, v___x_4679_);
return v___x_4681_;
}
}
else
{
lean_object* v___x_4684_; 
lean_dec(v_k_4669_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4684_ = v___x_4674_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4677_);
lean_ctor_set_uint8(v_reuseFailAlloc_4685_, sizeof(void*)*1, v_hasTrace_4672_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object* v_o_4687_, lean_object* v_k_4688_, lean_object* v_v_4689_){
_start:
{
uint8_t v_v_boxed_4690_; lean_object* v_res_4691_; 
v_v_boxed_4690_ = lean_unbox(v_v_4689_);
v_res_4691_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_o_4687_, v_k_4688_, v_v_boxed_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4692_, lean_object* v_opt_4693_, uint8_t v_val_4694_){
_start:
{
lean_object* v_name_4695_; lean_object* v___x_4696_; 
v_name_4695_ = lean_ctor_get(v_opt_4693_, 0);
lean_inc(v_name_4695_);
lean_dec_ref(v_opt_4693_);
v___x_4696_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_opts_4692_, v_name_4695_, v_val_4694_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4697_, lean_object* v_opt_4698_, lean_object* v_val_4699_){
_start:
{
uint8_t v_val_boxed_4700_; lean_object* v_res_4701_; 
v_val_boxed_4700_ = lean_unbox(v_val_4699_);
v_res_4701_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4697_, v_opt_4698_, v_val_boxed_4700_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object* v_cls_4702_, lean_object* v_msg_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_ref_4709_; lean_object* v___x_4710_; lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4755_; 
v_ref_4709_ = lean_ctor_get(v___y_4706_, 5);
v___x_4710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4755_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4755_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4715_; lean_object* v_traceState_4716_; lean_object* v_env_4717_; lean_object* v_nextMacroScope_4718_; lean_object* v_ngen_4719_; lean_object* v_auxDeclNGen_4720_; lean_object* v_cache_4721_; lean_object* v_messages_4722_; lean_object* v_infoState_4723_; lean_object* v_snapshotTasks_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4754_; 
v___x_4715_ = lean_st_ref_take(v___y_4707_);
v_traceState_4716_ = lean_ctor_get(v___x_4715_, 4);
v_env_4717_ = lean_ctor_get(v___x_4715_, 0);
v_nextMacroScope_4718_ = lean_ctor_get(v___x_4715_, 1);
v_ngen_4719_ = lean_ctor_get(v___x_4715_, 2);
v_auxDeclNGen_4720_ = lean_ctor_get(v___x_4715_, 3);
v_cache_4721_ = lean_ctor_get(v___x_4715_, 5);
v_messages_4722_ = lean_ctor_get(v___x_4715_, 6);
v_infoState_4723_ = lean_ctor_get(v___x_4715_, 7);
v_snapshotTasks_4724_ = lean_ctor_get(v___x_4715_, 8);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4726_ = v___x_4715_;
v_isShared_4727_ = v_isSharedCheck_4754_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_snapshotTasks_4724_);
lean_inc(v_infoState_4723_);
lean_inc(v_messages_4722_);
lean_inc(v_cache_4721_);
lean_inc(v_traceState_4716_);
lean_inc(v_auxDeclNGen_4720_);
lean_inc(v_ngen_4719_);
lean_inc(v_nextMacroScope_4718_);
lean_inc(v_env_4717_);
lean_dec(v___x_4715_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4754_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
uint64_t v_tid_4728_; lean_object* v_traces_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4753_; 
v_tid_4728_ = lean_ctor_get_uint64(v_traceState_4716_, sizeof(void*)*1);
v_traces_4729_ = lean_ctor_get(v_traceState_4716_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_traceState_4716_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4731_ = v_traceState_4716_;
v_isShared_4732_ = v_isSharedCheck_4753_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_traces_4729_);
lean_dec(v_traceState_4716_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4753_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; double v___x_4734_; uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4733_ = lean_box(0);
v___x_4734_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0);
v___x_4735_ = 0;
v___x_4736_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_4737_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4737_, 0, v_cls_4702_);
lean_ctor_set(v___x_4737_, 1, v___x_4733_);
lean_ctor_set(v___x_4737_, 2, v___x_4736_);
lean_ctor_set_float(v___x_4737_, sizeof(void*)*3, v___x_4734_);
lean_ctor_set_float(v___x_4737_, sizeof(void*)*3 + 8, v___x_4734_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*3 + 16, v___x_4735_);
v___x_4738_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2));
v___x_4739_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
lean_ctor_set(v___x_4739_, 1, v_a_4711_);
lean_ctor_set(v___x_4739_, 2, v___x_4738_);
lean_inc(v_ref_4709_);
v___x_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4740_, 0, v_ref_4709_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = l_Lean_PersistentArray_push___redArg(v_traces_4729_, v___x_4740_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4741_);
v___x_4743_ = v___x_4731_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4741_);
lean_ctor_set_uint64(v_reuseFailAlloc_4752_, sizeof(void*)*1, v_tid_4728_);
v___x_4743_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4745_; 
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 4, v___x_4743_);
v___x_4745_ = v___x_4726_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_env_4717_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_nextMacroScope_4718_);
lean_ctor_set(v_reuseFailAlloc_4751_, 2, v_ngen_4719_);
lean_ctor_set(v_reuseFailAlloc_4751_, 3, v_auxDeclNGen_4720_);
lean_ctor_set(v_reuseFailAlloc_4751_, 4, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4751_, 5, v_cache_4721_);
lean_ctor_set(v_reuseFailAlloc_4751_, 6, v_messages_4722_);
lean_ctor_set(v_reuseFailAlloc_4751_, 7, v_infoState_4723_);
lean_ctor_set(v_reuseFailAlloc_4751_, 8, v_snapshotTasks_4724_);
v___x_4745_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4746_ = lean_st_ref_set(v___y_4707_, v___x_4745_);
v___x_4747_ = lean_box(0);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 0, v___x_4747_);
v___x_4749_ = v___x_4713_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object* v_cls_4756_, lean_object* v_msg_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v_cls_4756_, v_msg_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
return v_res_4763_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4767_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4768_ = lean_unsigned_to_nat(18u);
v___x_4769_ = lean_unsigned_to_nat(533u);
v___x_4770_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4771_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4772_ = l_mkPanicMessageWithDecl(v___x_4771_, v___x_4770_, v___x_4769_, v___x_4768_, v___x_4767_);
return v___x_4772_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4773_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4774_ = lean_unsigned_to_nat(2u);
v___x_4775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
lean_ctor_set(v___x_4775_, 1, v___x_4773_);
return v___x_4775_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4776_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4777_ = lean_box(1);
v___x_4778_ = lean_unsigned_to_nat(0u);
v___x_4779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
lean_ctor_set(v___x_4779_, 1, v___x_4777_);
lean_ctor_set(v___x_4779_, 2, v___x_4776_);
return v___x_4779_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4785_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_4787_ = l_Lean_Name_append(v___x_4786_, v___x_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4788_, lean_object* v_optionsPerPos_4789_, lean_object* v_delab_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_fst_4797_; lean_object* v_snd_4798_; lean_object* v___y_4803_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___y_4806_; lean_object* v___y_4807_; lean_object* v___y_4808_; uint8_t v___y_4809_; lean_object* v___y_4829_; lean_object* v___y_4830_; lean_object* v_optionsPerPos_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4869_; lean_object* v_e_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4888_; lean_object* v_e_4889_; lean_object* v___y_4890_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v___x_4905_; 
v___x_4905_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4788_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_5033_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_4908_ = v___x_4905_;
v_isShared_4909_ = v_isSharedCheck_5033_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4905_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_5033_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___y_4911_; uint8_t v___y_4912_; lean_object* v___y_4913_; uint8_t v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; uint8_t v___y_4940_; uint8_t v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; uint8_t v___y_4944_; lean_object* v_opts_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; uint8_t v___y_4984_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; uint8_t v___y_4995_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v_options_5008_; lean_object* v___y_5009_; lean_object* v_options_5015_; uint8_t v_hasTrace_5016_; 
v_options_5015_ = lean_ctor_get(v_a_4793_, 2);
v_hasTrace_5016_ = lean_ctor_get_uint8(v_options_5015_, sizeof(void*)*1);
if (v_hasTrace_5016_ == 0)
{
v___y_5005_ = v_a_4791_;
v___y_5006_ = v_a_4792_;
v___y_5007_ = v_a_4793_;
v_options_5008_ = v_options_5015_;
v___y_5009_ = v_a_4794_;
goto v___jp_5004_;
}
else
{
lean_object* v_inheritedTraceOptions_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v_inheritedTraceOptions_5017_ = lean_ctor_get(v_a_4793_, 13);
v___x_5018_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5019_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5017_, v_options_5015_, v___x_5019_);
if (v___x_5020_ == 0)
{
v___y_5005_ = v_a_4791_;
v___y_5006_ = v_a_4792_;
v___y_5007_ = v_a_4793_;
v_options_5008_ = v_options_5015_;
v___y_5009_ = v_a_4794_;
goto v___jp_5004_;
}
else
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5021_ = lean_expr_dbg_to_string(v_a_4906_);
v___x_5022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
v___x_5023_ = l_Lean_MessageData_ofFormat(v___x_5022_);
v___x_5024_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v___x_5018_, v___x_5023_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_dec_ref_known(v___x_5024_, 1);
v___y_5005_ = v_a_4791_;
v___y_5006_ = v_a_4792_;
v___y_5007_ = v_a_4793_;
v_options_5008_ = v_options_5015_;
v___y_5009_ = v_a_4794_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_del_object(v___x_4908_);
lean_dec(v_a_4906_);
lean_dec_ref(v_delab_4790_);
lean_dec(v_optionsPerPos_4789_);
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5024_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
}
v___jp_4910_:
{
lean_object* v_fileName_4918_; lean_object* v_fileMap_4919_; lean_object* v_currRecDepth_4920_; lean_object* v_ref_4921_; lean_object* v_currNamespace_4922_; lean_object* v_openDecls_4923_; lean_object* v_initHeartbeats_4924_; lean_object* v_maxHeartbeats_4925_; lean_object* v_quotContext_4926_; lean_object* v_currMacroScope_4927_; lean_object* v_cancelTk_x3f_4928_; uint8_t v_suppressElabErrors_4929_; lean_object* v_inheritedTraceOptions_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_fileName_4918_ = lean_ctor_get(v___y_4916_, 0);
v_fileMap_4919_ = lean_ctor_get(v___y_4916_, 1);
v_currRecDepth_4920_ = lean_ctor_get(v___y_4916_, 3);
v_ref_4921_ = lean_ctor_get(v___y_4916_, 5);
v_currNamespace_4922_ = lean_ctor_get(v___y_4916_, 6);
v_openDecls_4923_ = lean_ctor_get(v___y_4916_, 7);
v_initHeartbeats_4924_ = lean_ctor_get(v___y_4916_, 8);
v_maxHeartbeats_4925_ = lean_ctor_get(v___y_4916_, 9);
v_quotContext_4926_ = lean_ctor_get(v___y_4916_, 10);
v_currMacroScope_4927_ = lean_ctor_get(v___y_4916_, 11);
v_cancelTk_x3f_4928_ = lean_ctor_get(v___y_4916_, 12);
v_suppressElabErrors_4929_ = lean_ctor_get_uint8(v___y_4916_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4930_ = lean_ctor_get(v___y_4916_, 13);
v___x_4931_ = l_Lean_maxRecDepth;
v___x_4932_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v___y_4911_, v___x_4931_);
lean_inc_ref(v_inheritedTraceOptions_4930_);
lean_inc(v_cancelTk_x3f_4928_);
lean_inc(v_currMacroScope_4927_);
lean_inc(v_quotContext_4926_);
lean_inc(v_maxHeartbeats_4925_);
lean_inc(v_initHeartbeats_4924_);
lean_inc(v_openDecls_4923_);
lean_inc(v_currNamespace_4922_);
lean_inc(v_ref_4921_);
lean_inc(v_currRecDepth_4920_);
lean_inc_ref(v___y_4911_);
lean_inc_ref(v_fileMap_4919_);
lean_inc_ref(v_fileName_4918_);
v___x_4933_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4933_, 0, v_fileName_4918_);
lean_ctor_set(v___x_4933_, 1, v_fileMap_4919_);
lean_ctor_set(v___x_4933_, 2, v___y_4911_);
lean_ctor_set(v___x_4933_, 3, v_currRecDepth_4920_);
lean_ctor_set(v___x_4933_, 4, v___x_4932_);
lean_ctor_set(v___x_4933_, 5, v_ref_4921_);
lean_ctor_set(v___x_4933_, 6, v_currNamespace_4922_);
lean_ctor_set(v___x_4933_, 7, v_openDecls_4923_);
lean_ctor_set(v___x_4933_, 8, v_initHeartbeats_4924_);
lean_ctor_set(v___x_4933_, 9, v_maxHeartbeats_4925_);
lean_ctor_set(v___x_4933_, 10, v_quotContext_4926_);
lean_ctor_set(v___x_4933_, 11, v_currMacroScope_4927_);
lean_ctor_set(v___x_4933_, 12, v_cancelTk_x3f_4928_);
lean_ctor_set(v___x_4933_, 13, v_inheritedTraceOptions_4930_);
lean_ctor_set_uint8(v___x_4933_, sizeof(void*)*14, v___y_4912_);
lean_ctor_set_uint8(v___x_4933_, sizeof(void*)*14 + 1, v_suppressElabErrors_4929_);
if (v___y_4914_ == 0)
{
v___y_4888_ = v___y_4911_;
v_e_4889_ = v_a_4906_;
v___y_4890_ = v___y_4915_;
v___y_4891_ = v___y_4913_;
v___y_4892_ = v___x_4933_;
v___y_4893_ = v___y_4917_;
goto v___jp_4887_;
}
else
{
lean_object* v___x_4934_; lean_object* v_a_4935_; 
v___x_4934_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_a_4906_, v___y_4913_);
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref(v___x_4934_);
v___y_4888_ = v___y_4911_;
v_e_4889_ = v_a_4935_;
v___y_4890_ = v___y_4915_;
v___y_4891_ = v___y_4913_;
v___y_4892_ = v___x_4933_;
v___y_4893_ = v___y_4917_;
goto v___jp_4887_;
}
}
v___jp_4936_:
{
if (v___y_4944_ == 0)
{
lean_object* v___x_4945_; lean_object* v_env_4946_; lean_object* v_nextMacroScope_4947_; lean_object* v_ngen_4948_; lean_object* v_auxDeclNGen_4949_; lean_object* v_traceState_4950_; lean_object* v_messages_4951_; lean_object* v_infoState_4952_; lean_object* v_snapshotTasks_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4963_; 
v___x_4945_ = lean_st_ref_take(v___y_4939_);
v_env_4946_ = lean_ctor_get(v___x_4945_, 0);
v_nextMacroScope_4947_ = lean_ctor_get(v___x_4945_, 1);
v_ngen_4948_ = lean_ctor_get(v___x_4945_, 2);
v_auxDeclNGen_4949_ = lean_ctor_get(v___x_4945_, 3);
v_traceState_4950_ = lean_ctor_get(v___x_4945_, 4);
v_messages_4951_ = lean_ctor_get(v___x_4945_, 6);
v_infoState_4952_ = lean_ctor_get(v___x_4945_, 7);
v_snapshotTasks_4953_ = lean_ctor_get(v___x_4945_, 8);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4963_ == 0)
{
lean_object* v_unused_4964_; 
v_unused_4964_ = lean_ctor_get(v___x_4945_, 5);
lean_dec(v_unused_4964_);
v___x_4955_ = v___x_4945_;
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_snapshotTasks_4953_);
lean_inc(v_infoState_4952_);
lean_inc(v_messages_4951_);
lean_inc(v_traceState_4950_);
lean_inc(v_auxDeclNGen_4949_);
lean_inc(v_ngen_4948_);
lean_inc(v_nextMacroScope_4947_);
lean_inc(v_env_4946_);
lean_dec(v___x_4945_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4960_; 
v___x_4957_ = l_Lean_Kernel_enableDiag(v_env_4946_, v___y_4940_);
v___x_4958_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 5, v___x_4958_);
lean_ctor_set(v___x_4955_, 0, v___x_4957_);
v___x_4960_ = v___x_4955_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_nextMacroScope_4947_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_ngen_4948_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_auxDeclNGen_4949_);
lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_traceState_4950_);
lean_ctor_set(v_reuseFailAlloc_4962_, 5, v___x_4958_);
lean_ctor_set(v_reuseFailAlloc_4962_, 6, v_messages_4951_);
lean_ctor_set(v_reuseFailAlloc_4962_, 7, v_infoState_4952_);
lean_ctor_set(v_reuseFailAlloc_4962_, 8, v_snapshotTasks_4953_);
v___x_4960_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
lean_object* v___x_4961_; 
v___x_4961_ = lean_st_ref_set(v___y_4939_, v___x_4960_);
v___y_4911_ = v___y_4938_;
v___y_4912_ = v___y_4940_;
v___y_4913_ = v___y_4942_;
v___y_4914_ = v___y_4941_;
v___y_4915_ = v___y_4943_;
v___y_4916_ = v___y_4937_;
v___y_4917_ = v___y_4939_;
goto v___jp_4910_;
}
}
}
else
{
v___y_4911_ = v___y_4938_;
v___y_4912_ = v___y_4940_;
v___y_4913_ = v___y_4942_;
v___y_4914_ = v___y_4941_;
v___y_4915_ = v___y_4943_;
v___y_4916_ = v___y_4937_;
v___y_4917_ = v___y_4939_;
goto v___jp_4910_;
}
}
v___jp_4965_:
{
lean_object* v___x_4971_; lean_object* v_env_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; uint8_t v___x_4975_; uint8_t v___x_4976_; 
v___x_4971_ = lean_st_ref_get(v___y_4970_);
v_env_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc_ref(v_env_4972_);
lean_dec(v___x_4971_);
v___x_4973_ = l_Lean_getPPInstantiateMVars(v_opts_4966_);
v___x_4974_ = l_Lean_diagnostics;
v___x_4975_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4966_, v___x_4974_);
v___x_4976_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4972_);
lean_dec_ref(v_env_4972_);
if (v___x_4976_ == 0)
{
if (v___x_4975_ == 0)
{
v___y_4911_ = v_opts_4966_;
v___y_4912_ = v___x_4975_;
v___y_4913_ = v___y_4968_;
v___y_4914_ = v___x_4973_;
v___y_4915_ = v___y_4967_;
v___y_4916_ = v___y_4969_;
v___y_4917_ = v___y_4970_;
goto v___jp_4910_;
}
else
{
v___y_4937_ = v___y_4969_;
v___y_4938_ = v_opts_4966_;
v___y_4939_ = v___y_4970_;
v___y_4940_ = v___x_4975_;
v___y_4941_ = v___x_4973_;
v___y_4942_ = v___y_4968_;
v___y_4943_ = v___y_4967_;
v___y_4944_ = v___x_4976_;
goto v___jp_4936_;
}
}
else
{
v___y_4937_ = v___y_4969_;
v___y_4938_ = v_opts_4966_;
v___y_4939_ = v___y_4970_;
v___y_4940_ = v___x_4975_;
v___y_4941_ = v___x_4973_;
v___y_4942_ = v___y_4968_;
v___y_4943_ = v___y_4967_;
v___y_4944_ = v___x_4975_;
goto v___jp_4936_;
}
}
v___jp_4977_:
{
if (v___y_4984_ == 0)
{
lean_dec_ref(v___y_4981_);
lean_del_object(v___x_4908_);
lean_inc_ref(v___y_4980_);
v_opts_4966_ = v___y_4980_;
v___y_4967_ = v___y_4979_;
v___y_4968_ = v___y_4983_;
v___y_4969_ = v___y_4982_;
v___y_4970_ = v___y_4978_;
goto v___jp_4965_;
}
else
{
lean_object* v___x_4986_; 
lean_dec(v_a_4906_);
lean_dec_ref(v_delab_4790_);
lean_dec(v_optionsPerPos_4789_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set_tag(v___x_4908_, 1);
lean_ctor_set(v___x_4908_, 0, v___y_4981_);
v___x_4986_ = v___x_4908_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___y_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
v___jp_4988_:
{
if (v___y_4995_ == 0)
{
lean_del_object(v___x_4908_);
lean_inc_ref(v___y_4992_);
v_opts_4966_ = v___y_4992_;
v___y_4967_ = v___y_4990_;
v___y_4968_ = v___y_4994_;
v___y_4969_ = v___y_4993_;
v___y_4970_ = v___y_4989_;
goto v___jp_4965_;
}
else
{
lean_object* v___x_4996_; 
lean_inc(v_a_4906_);
v___x_4996_ = l_Lean_Meta_isProof(v_a_4906_, v___y_4990_, v___y_4994_, v___y_4993_, v___y_4989_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; uint8_t v___x_4998_; 
lean_del_object(v___x_4908_);
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4996_, 1);
v___x_4998_ = lean_unbox(v_a_4997_);
if (v___x_4998_ == 0)
{
lean_dec(v_a_4997_);
lean_inc_ref(v___y_4992_);
v_opts_4966_ = v___y_4992_;
v___y_4967_ = v___y_4990_;
v___y_4968_ = v___y_4994_;
v___y_4969_ = v___y_4993_;
v___y_4970_ = v___y_4989_;
goto v___jp_4965_;
}
else
{
uint8_t v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = lean_unbox(v_a_4997_);
lean_dec(v_a_4997_);
lean_inc_ref(v___y_4991_);
lean_inc_ref(v___y_4992_);
v___x_5000_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v___y_4992_, v___y_4991_, v___x_4999_);
v_opts_4966_ = v___x_5000_;
v___y_4967_ = v___y_4990_;
v___y_4968_ = v___y_4994_;
v___y_4969_ = v___y_4993_;
v___y_4970_ = v___y_4989_;
goto v___jp_4965_;
}
}
else
{
lean_object* v_a_5001_; uint8_t v___x_5002_; 
v_a_5001_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_5001_);
lean_dec_ref_known(v___x_4996_, 1);
v___x_5002_ = l_Lean_Exception_isInterrupt(v_a_5001_);
if (v___x_5002_ == 0)
{
uint8_t v___x_5003_; 
lean_inc(v_a_5001_);
v___x_5003_ = l_Lean_Exception_isRuntime(v_a_5001_);
v___y_4978_ = v___y_4989_;
v___y_4979_ = v___y_4990_;
v___y_4980_ = v___y_4992_;
v___y_4981_ = v_a_5001_;
v___y_4982_ = v___y_4993_;
v___y_4983_ = v___y_4994_;
v___y_4984_ = v___x_5003_;
goto v___jp_4977_;
}
else
{
v___y_4978_ = v___y_4989_;
v___y_4979_ = v___y_4990_;
v___y_4980_ = v___y_4992_;
v___y_4981_ = v_a_5001_;
v___y_4982_ = v___y_4993_;
v___y_4983_ = v___y_4994_;
v___y_4984_ = v___x_5002_;
goto v___jp_4977_;
}
}
}
}
v___jp_5004_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5010_ = l_Lean_pp_proofs;
v___x_5011_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_options_5008_, v___x_5010_);
v___x_5012_ = lean_box(0);
v___x_5013_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5011_, v___x_5012_);
lean_dec(v___x_5011_);
if (v___x_5013_ == 0)
{
v___y_4989_ = v___y_5009_;
v___y_4990_ = v___y_5005_;
v___y_4991_ = v___x_5010_;
v___y_4992_ = v_options_5008_;
v___y_4993_ = v___y_5007_;
v___y_4994_ = v___y_5006_;
v___y_4995_ = v___x_5013_;
goto v___jp_4988_;
}
else
{
uint8_t v___x_5014_; 
v___x_5014_ = l_Lean_Expr_isConst(v_a_4906_);
if (v___x_5014_ == 0)
{
v___y_4989_ = v___y_5009_;
v___y_4990_ = v___y_5005_;
v___y_4991_ = v___x_5010_;
v___y_4992_ = v_options_5008_;
v___y_4993_ = v___y_5007_;
v___y_4994_ = v___y_5006_;
v___y_4995_ = v___x_5013_;
goto v___jp_4988_;
}
else
{
lean_del_object(v___x_4908_);
lean_inc_ref(v_options_5008_);
v_opts_4966_ = v_options_5008_;
v___y_4967_ = v___y_5005_;
v___y_4968_ = v___y_5006_;
v___y_4969_ = v___y_5007_;
v___y_4970_ = v___y_5009_;
goto v___jp_4965_;
}
}
}
}
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec_ref(v_delab_4790_);
lean_dec(v_optionsPerPos_4789_);
v_a_5034_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_4905_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_4905_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
v___jp_4796_:
{
lean_object* v_infos_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v_infos_4799_ = lean_ctor_get(v_snd_4798_, 1);
lean_inc(v_infos_4799_);
lean_dec_ref(v_snd_4798_);
v___x_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4800_, 0, v_fst_4797_);
lean_ctor_set(v___x_4800_, 1, v_infos_4799_);
v___x_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
return v___x_4801_;
}
v___jp_4802_:
{
if (v___y_4809_ == 0)
{
if (lean_obj_tag(v___y_4804_) == 0)
{
lean_object* v___x_4810_; 
lean_dec_ref(v___y_4808_);
v___x_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4810_, 0, v___y_4804_);
return v___x_4810_;
}
else
{
lean_object* v_id_4811_; uint8_t v___x_4812_; 
v_id_4811_ = lean_ctor_get(v___y_4804_, 0);
v___x_4812_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4803_, v_id_4811_);
if (v___x_4812_ == 0)
{
lean_object* v___x_4813_; 
lean_dec_ref(v___y_4808_);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___y_4804_);
return v___x_4813_;
}
else
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec_ref_known(v___y_4804_, 2);
v___x_4814_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4815_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4814_, v___y_4805_, v___y_4807_, v___y_4808_, v___y_4806_);
lean_dec_ref(v___y_4808_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v_fst_4817_; lean_object* v_snd_4818_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
lean_dec_ref_known(v___x_4815_, 1);
v_fst_4817_ = lean_ctor_get(v_a_4816_, 0);
lean_inc(v_fst_4817_);
v_snd_4818_ = lean_ctor_get(v_a_4816_, 1);
lean_inc(v_snd_4818_);
lean_dec(v_a_4816_);
v_fst_4797_ = v_fst_4817_;
v_snd_4798_ = v_snd_4818_;
goto v___jp_4796_;
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_a_4819_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4815_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4815_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
}
else
{
lean_object* v___x_4827_; 
lean_dec_ref(v___y_4808_);
v___x_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___y_4804_);
return v___x_4827_;
}
}
v___jp_4828_:
{
lean_object* v_fileName_4836_; lean_object* v_fileMap_4837_; lean_object* v_options_4838_; lean_object* v_currRecDepth_4839_; lean_object* v_maxRecDepth_4840_; lean_object* v_currNamespace_4841_; lean_object* v_openDecls_4842_; lean_object* v_initHeartbeats_4843_; lean_object* v_maxHeartbeats_4844_; lean_object* v_quotContext_4845_; lean_object* v_currMacroScope_4846_; uint8_t v_diag_4847_; lean_object* v_cancelTk_x3f_4848_; uint8_t v_suppressElabErrors_4849_; lean_object* v_inheritedTraceOptions_4850_; lean_object* v_lctx_4851_; uint8_t v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_fileName_4836_ = lean_ctor_get(v___y_4834_, 0);
v_fileMap_4837_ = lean_ctor_get(v___y_4834_, 1);
v_options_4838_ = lean_ctor_get(v___y_4834_, 2);
v_currRecDepth_4839_ = lean_ctor_get(v___y_4834_, 3);
v_maxRecDepth_4840_ = lean_ctor_get(v___y_4834_, 4);
v_currNamespace_4841_ = lean_ctor_get(v___y_4834_, 6);
v_openDecls_4842_ = lean_ctor_get(v___y_4834_, 7);
v_initHeartbeats_4843_ = lean_ctor_get(v___y_4834_, 8);
v_maxHeartbeats_4844_ = lean_ctor_get(v___y_4834_, 9);
v_quotContext_4845_ = lean_ctor_get(v___y_4834_, 10);
v_currMacroScope_4846_ = lean_ctor_get(v___y_4834_, 11);
v_diag_4847_ = lean_ctor_get_uint8(v___y_4834_, sizeof(void*)*14);
v_cancelTk_x3f_4848_ = lean_ctor_get(v___y_4834_, 12);
v_suppressElabErrors_4849_ = lean_ctor_get_uint8(v___y_4834_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4850_ = lean_ctor_get(v___y_4834_, 13);
v_lctx_4851_ = lean_ctor_get(v___y_4832_, 2);
v___x_4852_ = l_Lean_Options_getInPattern(v___y_4829_);
lean_dec_ref(v___y_4829_);
v___x_4853_ = l_Lean_SubExpr_mkRoot(v___y_4830_);
v___x_4854_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4851_);
v___x_4855_ = lean_local_ctx_num_indices(v_lctx_4851_);
lean_inc_n(v_openDecls_4842_, 2);
lean_inc_n(v_currNamespace_4841_, 2);
v___x_4856_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4856_, 0, v_optionsPerPos_4831_);
lean_ctor_set(v___x_4856_, 1, v_currNamespace_4841_);
lean_ctor_set(v___x_4856_, 2, v_openDecls_4842_);
lean_ctor_set(v___x_4856_, 3, v___x_4853_);
lean_ctor_set(v___x_4856_, 4, v___x_4854_);
lean_ctor_set(v___x_4856_, 5, v___x_4855_);
lean_ctor_set_uint8(v___x_4856_, sizeof(void*)*6, v___x_4852_);
v___x_4857_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4858_ = lean_st_mk_ref(v___x_4857_);
v___x_4859_ = lean_box(0);
lean_inc_ref(v_inheritedTraceOptions_4850_);
lean_inc(v_cancelTk_x3f_4848_);
lean_inc(v_currMacroScope_4846_);
lean_inc(v_quotContext_4845_);
lean_inc(v_maxHeartbeats_4844_);
lean_inc(v_initHeartbeats_4843_);
lean_inc(v_maxRecDepth_4840_);
lean_inc(v_currRecDepth_4839_);
lean_inc_ref(v_options_4838_);
lean_inc_ref(v_fileMap_4837_);
lean_inc_ref(v_fileName_4836_);
v___x_4860_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4860_, 0, v_fileName_4836_);
lean_ctor_set(v___x_4860_, 1, v_fileMap_4837_);
lean_ctor_set(v___x_4860_, 2, v_options_4838_);
lean_ctor_set(v___x_4860_, 3, v_currRecDepth_4839_);
lean_ctor_set(v___x_4860_, 4, v_maxRecDepth_4840_);
lean_ctor_set(v___x_4860_, 5, v___x_4859_);
lean_ctor_set(v___x_4860_, 6, v_currNamespace_4841_);
lean_ctor_set(v___x_4860_, 7, v_openDecls_4842_);
lean_ctor_set(v___x_4860_, 8, v_initHeartbeats_4843_);
lean_ctor_set(v___x_4860_, 9, v_maxHeartbeats_4844_);
lean_ctor_set(v___x_4860_, 10, v_quotContext_4845_);
lean_ctor_set(v___x_4860_, 11, v_currMacroScope_4846_);
lean_ctor_set(v___x_4860_, 12, v_cancelTk_x3f_4848_);
lean_ctor_set(v___x_4860_, 13, v_inheritedTraceOptions_4850_);
lean_ctor_set_uint8(v___x_4860_, sizeof(void*)*14, v_diag_4847_);
lean_ctor_set_uint8(v___x_4860_, sizeof(void*)*14 + 1, v_suppressElabErrors_4849_);
lean_inc(v___y_4835_);
lean_inc(v___y_4833_);
lean_inc_ref(v___y_4832_);
lean_inc(v___x_4858_);
v___x_4861_ = lean_apply_7(v_delab_4790_, v___x_4856_, v___x_4858_, v___y_4832_, v___y_4833_, v___x_4860_, v___y_4835_, lean_box(0));
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; 
lean_dec_ref(v___y_4834_);
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = lean_st_ref_get(v___x_4858_);
lean_dec(v___x_4858_);
v_fst_4797_ = v_a_4862_;
v_snd_4798_ = v___x_4863_;
goto v___jp_4796_;
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; 
lean_dec(v___x_4858_);
v_a_4864_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4865_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4866_ = l_Lean_Exception_isInterrupt(v_a_4864_);
if (v___x_4866_ == 0)
{
uint8_t v___x_4867_; 
lean_inc(v_a_4864_);
v___x_4867_ = l_Lean_Exception_isRuntime(v_a_4864_);
v___y_4803_ = v___x_4865_;
v___y_4804_ = v_a_4864_;
v___y_4805_ = v___y_4832_;
v___y_4806_ = v___y_4835_;
v___y_4807_ = v___y_4833_;
v___y_4808_ = v___y_4834_;
v___y_4809_ = v___x_4867_;
goto v___jp_4802_;
}
else
{
v___y_4803_ = v___x_4865_;
v___y_4804_ = v_a_4864_;
v___y_4805_ = v___y_4832_;
v___y_4806_ = v___y_4835_;
v___y_4807_ = v___y_4833_;
v___y_4808_ = v___y_4834_;
v___y_4809_ = v___x_4866_;
goto v___jp_4802_;
}
}
}
v___jp_4868_:
{
uint8_t v___x_4875_; 
v___x_4875_ = l_Lean_getPPAll(v___y_4869_);
if (v___x_4875_ == 0)
{
uint8_t v___x_4876_; 
v___x_4876_ = l_Lean_getPPAnalyze(v___y_4869_);
if (v___x_4876_ == 0)
{
v___y_4829_ = v___y_4869_;
v___y_4830_ = v_e_4870_;
v_optionsPerPos_4831_ = v_optionsPerPos_4789_;
v___y_4832_ = v___y_4871_;
v___y_4833_ = v___y_4872_;
v___y_4834_ = v___y_4873_;
v___y_4835_ = v___y_4874_;
goto v___jp_4828_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4789_) == 0)
{
v___y_4829_ = v___y_4869_;
v___y_4830_ = v_e_4870_;
v_optionsPerPos_4831_ = v_optionsPerPos_4789_;
v___y_4832_ = v___y_4871_;
v___y_4833_ = v___y_4872_;
v___y_4834_ = v___y_4873_;
v___y_4835_ = v___y_4874_;
goto v___jp_4828_;
}
else
{
lean_object* v___x_4877_; 
lean_inc_ref(v_e_4870_);
v___x_4877_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v___y_4829_ = v___y_4869_;
v___y_4830_ = v_e_4870_;
v_optionsPerPos_4831_ = v_a_4878_;
v___y_4832_ = v___y_4871_;
v___y_4833_ = v___y_4872_;
v___y_4834_ = v___y_4873_;
v___y_4835_ = v___y_4874_;
goto v___jp_4828_;
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec_ref(v___y_4873_);
lean_dec_ref(v_e_4870_);
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_delab_4790_);
v_a_4879_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4877_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4877_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
}
else
{
v___y_4829_ = v___y_4869_;
v___y_4830_ = v_e_4870_;
v_optionsPerPos_4831_ = v_optionsPerPos_4789_;
v___y_4832_ = v___y_4871_;
v___y_4833_ = v___y_4872_;
v___y_4834_ = v___y_4873_;
v___y_4835_ = v___y_4874_;
goto v___jp_4828_;
}
}
v___jp_4887_:
{
uint8_t v___x_4894_; 
v___x_4894_ = l_Lean_getPPBeta(v___y_4888_);
if (v___x_4894_ == 0)
{
v___y_4869_ = v___y_4888_;
v_e_4870_ = v_e_4889_;
v___y_4871_ = v___y_4890_;
v___y_4872_ = v___y_4891_;
v___y_4873_ = v___y_4892_;
v___y_4874_ = v___y_4893_;
goto v___jp_4868_;
}
else
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_Core_betaReduce(v_e_4889_, v___y_4892_, v___y_4893_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref_known(v___x_4895_, 1);
v___y_4869_ = v___y_4888_;
v_e_4870_ = v_a_4896_;
v___y_4871_ = v___y_4890_;
v___y_4872_ = v___y_4891_;
v___y_4873_ = v___y_4892_;
v___y_4874_ = v___y_4893_;
goto v___jp_4868_;
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec_ref(v___y_4892_);
lean_dec_ref(v___y_4888_);
lean_dec_ref(v_delab_4790_);
lean_dec(v_optionsPerPos_4789_);
v_a_4897_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4895_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4895_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5042_, lean_object* v_optionsPerPos_5043_, lean_object* v_delab_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5042_, v_optionsPerPos_5043_, v_delab_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5051_, lean_object* v_e_5052_, lean_object* v_optionsPerPos_5053_, lean_object* v_delab_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5052_, v_optionsPerPos_5053_, v_delab_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5061_, lean_object* v_e_5062_, lean_object* v_optionsPerPos_5063_, lean_object* v_delab_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5061_, v_e_5062_, v_optionsPerPos_5063_, v_delab_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5072_, lean_object* v_optionsPerPos_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5079_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5080_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5072_, v_optionsPerPos_5073_, v___x_5079_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5089_; 
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5083_ = v___x_5080_;
v_isShared_5084_ = v_isSharedCheck_5089_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5080_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5089_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v_fst_5085_; lean_object* v___x_5087_; 
v_fst_5085_ = lean_ctor_get(v_a_5081_, 0);
lean_inc(v_fst_5085_);
lean_dec(v_a_5081_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 0, v_fst_5085_);
v___x_5087_ = v___x_5083_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_fst_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
v_a_5090_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5080_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5080_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5098_, lean_object* v_optionsPerPos_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_PrettyPrinter_delab(v_e_5098_, v_optionsPerPos_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5170_; uint8_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5170_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5171_ = 0;
v___x_5172_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5173_ = l_Lean_registerTraceClass(v___x_5170_, v___x_5171_, v___x_5172_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v___x_5174_; lean_object* v___x_5175_; 
lean_dec_ref_known(v___x_5173_, 1);
v___x_5174_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5175_ = l_Lean_registerTraceClass(v___x_5174_, v___x_5171_, v___x_5172_);
return v___x_5175_;
}
else
{
return v___x_5173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5177_;
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
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
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
