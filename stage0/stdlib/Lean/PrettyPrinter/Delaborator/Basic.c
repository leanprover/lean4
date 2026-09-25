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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_PersistentHashMap_empty___redArg();
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
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_getPPProofs___boxed(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_getPPProofsThreshold___boxed(lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0;
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
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_orElse___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1_value;
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
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 512, .m_capacity = 512, .m_length = 511, .m_data = "Registers a delaborator.\n\n`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the\n`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`, elaborators\nfor `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\") to reduce\nspecial casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first."};
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
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 619, .m_capacity = 619, .m_length = 618, .m_data = "Registers an unexpander for applications of a given constant.\n\n`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant\n`c`. The unexpander is passed the result of pre-pretty printing the application *without*\nimplicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,\nit will not be called at all.\n\nUnexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without\nspecial imports. This however also makes them much less capable since they can only transform\nsyntax and don't have access to the expression tree."};
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
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0(lean_object* v___x_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_9_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0___boxed(lean_object* v___x_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0(v___x_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0(void){
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___f_31_; 
v___x_30_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0, &l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__0);
v___f_31_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg(){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1, &l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___closed__1);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg___boxed(lean_object* v___dummy_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg();
return v_res_35_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___redArg();
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object* v_00_u03b1_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg(lean_object* v_d_u2081_39_, lean_object* v_d_u2082_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_46_);
lean_inc_ref(v_a_45_);
lean_inc(v_a_44_);
lean_inc_ref(v_a_43_);
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
v___x_49_ = lean_apply_7(v_d_u2081_39_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, lean_box(0));
if (lean_obj_tag(v___x_49_) == 0)
{
lean_dec_ref(v_d_u2082_40_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; uint8_t v___y_52_; uint8_t v___x_57_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v___x_57_ = l_Lean_Exception_isInterrupt(v_a_50_);
if (v___x_57_ == 0)
{
uint8_t v___x_58_; 
lean_inc(v_a_50_);
v___x_58_ = l_Lean_Exception_isRuntime(v_a_50_);
v___y_52_ = v___x_58_;
goto v___jp_51_;
}
else
{
v___y_52_ = v___x_57_;
goto v___jp_51_;
}
v___jp_51_:
{
if (v___y_52_ == 0)
{
if (lean_obj_tag(v_a_50_) == 0)
{
lean_dec_ref_known(v_a_50_, 2);
lean_dec_ref(v_d_u2082_40_);
return v___x_49_;
}
else
{
lean_object* v_id_53_; uint8_t v___x_54_; 
v_id_53_ = lean_ctor_get(v_a_50_, 0);
lean_inc(v_id_53_);
lean_dec_ref_known(v_a_50_, 2);
v___x_54_ = l_Lean_instBEqInternalExceptionId_beq(v___x_48_, v_id_53_);
lean_dec(v_id_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v_d_u2082_40_);
return v___x_49_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec_ref_known(v___x_49_, 1);
v___x_55_ = lean_box(0);
lean_inc(v_a_46_);
lean_inc_ref(v_a_45_);
lean_inc(v_a_44_);
lean_inc_ref(v_a_43_);
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
v___x_56_ = lean_apply_8(v_d_u2082_40_, v___x_55_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, lean_box(0));
return v___x_56_;
}
}
}
else
{
lean_dec(v_a_50_);
lean_dec_ref(v_d_u2082_40_);
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg___boxed(lean_object* v_d_u2081_59_, lean_object* v_d_u2082_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_PrettyPrinter_Delaborator_orElse___redArg(v_d_u2081_59_, v_d_u2082_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object* v_00_u03b1_69_, lean_object* v_d_u2081_70_, lean_object* v_d_u2082_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
v___x_80_ = lean_apply_7(v_d_u2081_70_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, lean_box(0));
if (lean_obj_tag(v___x_80_) == 0)
{
lean_dec_ref(v_d_u2082_71_);
return v___x_80_;
}
else
{
lean_object* v_a_81_; uint8_t v___y_83_; uint8_t v___x_88_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
v___x_88_ = l_Lean_Exception_isInterrupt(v_a_81_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
lean_inc(v_a_81_);
v___x_89_ = l_Lean_Exception_isRuntime(v_a_81_);
v___y_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
v___y_83_ = v___x_88_;
goto v___jp_82_;
}
v___jp_82_:
{
if (v___y_83_ == 0)
{
if (lean_obj_tag(v_a_81_) == 0)
{
lean_dec_ref_known(v_a_81_, 2);
lean_dec_ref(v_d_u2082_71_);
return v___x_80_;
}
else
{
lean_object* v_id_84_; uint8_t v___x_85_; 
v_id_84_ = lean_ctor_get(v_a_81_, 0);
lean_inc(v_id_84_);
lean_dec_ref_known(v_a_81_, 2);
v___x_85_ = l_Lean_instBEqInternalExceptionId_beq(v___x_79_, v_id_84_);
lean_dec(v_id_84_);
if (v___x_85_ == 0)
{
lean_dec_ref(v_d_u2082_71_);
return v___x_80_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec_ref_known(v___x_80_, 1);
v___x_86_ = lean_box(0);
lean_inc(v_a_77_);
lean_inc_ref(v_a_76_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
v___x_87_ = lean_apply_8(v_d_u2082_71_, v___x_86_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, lean_box(0));
return v___x_87_;
}
}
}
else
{
lean_dec(v_a_81_);
lean_dec_ref(v_d_u2082_71_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___boxed(lean_object* v_00_u03b1_90_, lean_object* v_d_u2081_91_, lean_object* v_d_u2082_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_PrettyPrinter_Delaborator_orElse(v_00_u03b1_90_, v_d_u2081_91_, v_d_u2082_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_100_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_box(0);
v___x_102_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg(){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0, &l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg___boxed(lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object* v_00_u03b1_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object* v_00_u03b1_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_PrettyPrinter_Delaborator_failure(v_00_u03b1_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_126_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_instMonadEIO___redArg();
return v___x_127_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0);
v___x_129_ = l_StateRefT_x27_instMonad___redArg(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM(void){
_start:
{
lean_object* v___x_136_; lean_object* v_toApplicative_137_; lean_object* v_toFunctor_138_; lean_object* v_toSeq_139_; lean_object* v_toSeqLeft_140_; lean_object* v_toSeqRight_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_toApplicative_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_204_; 
v___x_136_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
v_toApplicative_137_ = lean_ctor_get(v___x_136_, 0);
v_toFunctor_138_ = lean_ctor_get(v_toApplicative_137_, 0);
v_toSeq_139_ = lean_ctor_get(v_toApplicative_137_, 2);
v_toSeqLeft_140_ = lean_ctor_get(v_toApplicative_137_, 3);
v_toSeqRight_141_ = lean_ctor_get(v_toApplicative_137_, 4);
v___f_142_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2));
v___f_143_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3));
lean_inc_ref_n(v_toFunctor_138_, 2);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_138_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toFunctor_138_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_144_);
lean_ctor_set(v___x_146_, 1, v___f_145_);
lean_inc(v_toSeqRight_141_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqRight_141_);
lean_inc(v_toSeqLeft_140_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeqLeft_140_);
lean_inc(v_toSeq_139_);
v___f_149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_149_, 0, v_toSeq_139_);
v___x_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_150_, 0, v___x_146_);
lean_ctor_set(v___x_150_, 1, v___f_142_);
lean_ctor_set(v___x_150_, 2, v___f_149_);
lean_ctor_set(v___x_150_, 3, v___f_148_);
lean_ctor_set(v___x_150_, 4, v___f_147_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___f_143_);
v___x_152_ = l_StateRefT_x27_instMonad___redArg(v___x_151_);
v_toApplicative_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v___x_152_, 1);
lean_dec(v_unused_205_);
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_204_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_toApplicative_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_204_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_toFunctor_157_; lean_object* v_toSeq_158_; lean_object* v_toSeqLeft_159_; lean_object* v_toSeqRight_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_202_; 
v_toFunctor_157_ = lean_ctor_get(v_toApplicative_153_, 0);
v_toSeq_158_ = lean_ctor_get(v_toApplicative_153_, 2);
v_toSeqLeft_159_ = lean_ctor_get(v_toApplicative_153_, 3);
v_toSeqRight_160_ = lean_ctor_get(v_toApplicative_153_, 4);
v_isSharedCheck_202_ = !lean_is_exclusive(v_toApplicative_153_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_toApplicative_153_, 1);
lean_dec(v_unused_203_);
v___x_162_ = v_toApplicative_153_;
v_isShared_163_ = v_isSharedCheck_202_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_toSeqRight_160_);
lean_inc(v_toSeqLeft_159_);
lean_inc(v_toSeq_158_);
lean_inc(v_toFunctor_157_);
lean_dec(v_toApplicative_153_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_202_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_173_; 
v___f_164_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4));
v___f_165_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5));
lean_inc_ref(v_toFunctor_157_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_166_, 0, v_toFunctor_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_167_, 0, v_toFunctor_157_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___f_166_);
lean_ctor_set(v___x_168_, 1, v___f_167_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_169_, 0, v_toSeqRight_160_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeqLeft_159_);
v___f_171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_171_, 0, v_toSeq_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 4, v___f_169_);
lean_ctor_set(v___x_162_, 3, v___f_170_);
lean_ctor_set(v___x_162_, 2, v___f_171_);
lean_ctor_set(v___x_162_, 1, v___f_164_);
lean_ctor_set(v___x_162_, 0, v___x_168_);
v___x_173_ = v___x_162_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___f_164_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___f_171_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v___f_170_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v___f_169_);
v___x_173_ = v_reuseFailAlloc_201_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___f_165_);
lean_ctor_set(v___x_155_, 0, v___x_173_);
v___x_175_ = v___x_155_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___f_165_);
v___x_175_ = v_reuseFailAlloc_200_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v_toApplicative_177_; lean_object* v_toFunctor_178_; lean_object* v_toSeq_179_; lean_object* v_toSeqLeft_180_; lean_object* v_toSeqRight_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_198_; 
v___x_176_ = l_StateRefT_x27_instMonad___redArg(v___x_175_);
v_toApplicative_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_toApplicative_177_);
v_toFunctor_178_ = lean_ctor_get(v_toApplicative_177_, 0);
v_toSeq_179_ = lean_ctor_get(v_toApplicative_177_, 2);
v_toSeqLeft_180_ = lean_ctor_get(v_toApplicative_177_, 3);
v_toSeqRight_181_ = lean_ctor_get(v_toApplicative_177_, 4);
v_isSharedCheck_198_ = !lean_is_exclusive(v_toApplicative_177_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_dec(v_unused_199_);
v___x_183_ = v_toApplicative_177_;
v_isShared_184_ = v_isSharedCheck_198_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_toSeqRight_181_);
lean_inc(v_toSeqLeft_180_);
lean_inc(v_toSeq_179_);
lean_inc(v_toFunctor_178_);
lean_dec(v_toApplicative_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_198_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeqRight_181_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_186_, 0, v_toSeqLeft_180_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_187_, 0, v_toSeq_179_);
lean_inc_ref(v_toFunctor_178_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_188_, 0, v_toFunctor_178_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_189_, 0, v_toFunctor_178_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___f_188_);
lean_ctor_set(v___x_190_, 1, v___f_189_);
v___x_191_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, lean_box(0));
lean_closure_set(v___x_191_, 2, v___x_176_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___f_185_);
lean_ctor_set(v___x_183_, 3, v___f_186_);
lean_ctor_set(v___x_183_, 2, v___f_187_);
lean_ctor_set(v___x_183_, 1, v___x_191_);
lean_ctor_set(v___x_183_, 0, v___x_190_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___f_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v___f_185_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6));
v___x_195_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7));
v___x_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_195_);
return v___x_196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg(){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___boxed(lean_object* v___dummy_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* v_00_u03b1_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0));
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_subExpr_220_; lean_object* v___x_221_; 
v_subExpr_220_ = lean_ctor_get(v___y_213_, 3);
lean_inc_ref(v_subExpr_220_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_subExpr_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed(lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(lean_object* v_00_u03b1_232_, lean_object* v_f_233_, lean_object* v_x_234_, lean_object* v_ctx_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_optionsPerPos_242_; lean_object* v_currNamespace_243_; lean_object* v_openDecls_244_; uint8_t v_inPattern_245_; lean_object* v_subExpr_246_; lean_object* v_depth_247_; lean_object* v_lctxInitIndices_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v_optionsPerPos_242_ = lean_ctor_get(v_ctx_235_, 0);
v_currNamespace_243_ = lean_ctor_get(v_ctx_235_, 1);
v_openDecls_244_ = lean_ctor_get(v_ctx_235_, 2);
v_inPattern_245_ = lean_ctor_get_uint8(v_ctx_235_, sizeof(void*)*6);
v_subExpr_246_ = lean_ctor_get(v_ctx_235_, 3);
v_depth_247_ = lean_ctor_get(v_ctx_235_, 4);
v_lctxInitIndices_248_ = lean_ctor_get(v_ctx_235_, 5);
v_isSharedCheck_257_ = !lean_is_exclusive(v_ctx_235_);
if (v_isSharedCheck_257_ == 0)
{
v___x_250_ = v_ctx_235_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_lctxInitIndices_248_);
lean_inc(v_depth_247_);
lean_inc(v_subExpr_246_);
lean_inc(v_openDecls_244_);
lean_inc(v_currNamespace_243_);
lean_inc(v_optionsPerPos_242_);
lean_dec(v_ctx_235_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_apply_1(v_f_233_, v_subExpr_246_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 3, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_optionsPerPos_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_currNamespace_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_openDecls_244_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_depth_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v_lctxInitIndices_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_256_, sizeof(void*)*6, v_inPattern_245_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
v___x_255_ = lean_apply_7(v_x_234_, v___x_254_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, lean_box(0));
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object* v_00_u03b1_258_, lean_object* v_f_259_, lean_object* v_x_260_, lean_object* v_ctx_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(v_00_u03b1_258_, v_f_259_, v_x_260_, v_ctx_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_holeIter_279_; lean_object* v___x_280_; 
v___x_278_ = lean_st_ref_get(v___y_272_);
v_holeIter_279_ = lean_ctor_get(v___x_278_, 2);
lean_inc_ref(v_holeIter_279_);
lean_dec(v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_holeIter_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object* v_iter_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_steps_298_; lean_object* v_infos_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v___x_297_ = lean_st_ref_take(v___y_291_);
v_steps_298_ = lean_ctor_get(v___x_297_, 0);
v_infos_299_ = lean_ctor_get(v___x_297_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_297_, 2);
lean_dec(v_unused_310_);
v___x_301_ = v___x_297_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_infos_299_);
lean_inc(v_steps_298_);
lean_dec(v___x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 2, v_iter_289_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_steps_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_infos_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_iter_289_);
v___x_305_ = v_reuseFailAlloc_308_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_st_ref_put(v___y_291_, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_303_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object* v_iter_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(v_iter_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object* v_00_u03b1_320_, lean_object* v_f_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_steps_330_; lean_object* v_infos_331_; lean_object* v_holeIter_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_344_; 
v___x_329_ = lean_st_ref_take(v___y_323_);
v_steps_330_ = lean_ctor_get(v___x_329_, 0);
v_infos_331_ = lean_ctor_get(v___x_329_, 1);
v_holeIter_332_ = lean_ctor_get(v___x_329_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_344_ == 0)
{
v___x_334_ = v___x_329_;
v_isShared_335_ = v_isSharedCheck_344_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_holeIter_332_);
lean_inc(v_infos_331_);
lean_inc(v_steps_330_);
lean_dec(v___x_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_344_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_340_; 
v___x_336_ = lean_apply_1(v_f_321_, v_holeIter_332_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_fst_337_);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_338_);
lean_dec_ref(v___x_336_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 2, v_snd_338_);
v___x_340_ = v___x_334_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_steps_330_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_infos_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_snd_338_);
v___x_340_ = v_reuseFailAlloc_343_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_st_ref_put(v___y_323_, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v_fst_337_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object* v_00_u03b1_345_, lean_object* v_f_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(v_00_u03b1_345_, v_f_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_builtin_363_, lean_object* v_declName_364_, lean_object* v_key_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_builtin_371_, lean_object* v_declName_372_, lean_object* v_key_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v_builtin_boxed_377_; lean_object* v_res_378_; 
v_builtin_boxed_377_ = lean_unbox(v_builtin_371_);
v_res_378_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_builtin_boxed_377_, v_declName_372_, v_key_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_key_373_);
lean_dec(v_declName_372_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v___x_383_);
lean_ctor_set(v___x_384_, 4, v___x_382_);
lean_ctor_set(v___x_384_, 5, v___x_382_);
lean_ctor_set(v___x_384_, 6, v___x_382_);
lean_ctor_set(v___x_384_, 7, v___x_382_);
lean_ctor_set(v___x_384_, 8, v___x_382_);
lean_ctor_set(v___x_384_, 9, v___x_382_);
lean_ctor_set(v___x_384_, 10, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_unsigned_to_nat(32u);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((size_t)5ULL);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_unsigned_to_nat(32u);
v___x_391_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_393_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_389_);
lean_ctor_set(v___x_393_, 3, v___x_389_);
lean_ctor_set_usize(v___x_393_, 4, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_box(1);
v___x_395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_419_, lean_object* v_declHint_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_env_425_; uint8_t v___x_426_; 
v___x_423_ = lean_box(0);
v___x_424_ = lean_st_ref_get(v___y_421_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_ref(v_env_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_Name_isAnonymous(v_declHint_420_);
if (v___x_426_ == 0)
{
uint8_t v_isExporting_427_; 
v_isExporting_427_ = lean_ctor_get_uint8(v_env_425_, sizeof(void*)*8);
if (v_isExporting_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v_env_425_);
lean_dec(v_declHint_420_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_msg_419_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; uint8_t v___x_430_; 
lean_inc_ref(v_env_425_);
v___x_429_ = l_Lean_Environment_setExporting(v_env_425_, v___x_426_);
lean_inc(v_declHint_420_);
lean_inc_ref(v___x_429_);
v___x_430_ = l_Lean_Environment_contains(v___x_429_, v_declHint_420_, v_isExporting_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec_ref(v___x_429_);
lean_dec_ref(v_env_425_);
lean_dec(v_declHint_420_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_msg_419_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_c_437_; lean_object* v___x_438_; 
v___x_432_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_434_ = l_Lean_Options_empty;
v___x_435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_435_, 0, v___x_429_);
lean_ctor_set(v___x_435_, 1, v___x_432_);
lean_ctor_set(v___x_435_, 2, v___x_433_);
lean_ctor_set(v___x_435_, 3, v___x_434_);
lean_inc(v_declHint_420_);
v___x_436_ = l_Lean_MessageData_ofConstName(v_declHint_420_, v___x_426_);
v_c_437_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_437_, 0, v___x_435_);
lean_ctor_set(v_c_437_, 1, v___x_436_);
v___x_438_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_425_, v_declHint_420_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v_env_425_);
lean_dec(v_declHint_420_);
v___x_439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_c_437_);
v___x_441_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_MessageData_note(v___x_442_);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v_msg_419_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_480_; 
v_val_446_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_480_ == 0)
{
v___x_448_ = v___x_438_;
v_isShared_449_ = v_isSharedCheck_480_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v___x_438_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_480_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_mod_452_; uint8_t v___x_453_; 
v___x_450_ = l_Lean_Environment_header(v_env_425_);
lean_dec_ref(v_env_425_);
v___x_451_ = l_Lean_EnvironmentHeader_moduleNames(v___x_450_);
v_mod_452_ = lean_array_get(v___x_423_, v___x_451_, v_val_446_);
lean_dec(v_val_446_);
lean_dec_ref(v___x_451_);
v___x_453_ = l_Lean_isPrivateName(v_declHint_420_);
lean_dec(v_declHint_420_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_454_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_c_437_);
v___x_456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_MessageData_ofName(v_mod_452_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_MessageData_note(v___x_461_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v_msg_419_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_463_);
v___x_465_ = v___x_448_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_c_437_);
v___x_469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_MessageData_ofName(v_mod_452_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_MessageData_note(v___x_474_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v_msg_419_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_476_);
v___x_478_ = v___x_448_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec_ref(v_env_425_);
lean_dec(v_declHint_420_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_msg_419_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_482_, lean_object* v_declHint_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_482_, v_declHint_483_, v___y_484_);
lean_dec(v___y_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object* v_msg_487_, lean_object* v_declHint_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v___x_492_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_487_, v_declHint_488_, v___y_490_);
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_502_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = l_Lean_unknownIdentifierMessageTag;
v___x_498_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_493_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_503_, lean_object* v_declHint_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_503_, v_declHint_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; lean_object* v_toCold_514_; lean_object* v_env_515_; lean_object* v_options_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_513_ = lean_st_ref_get(v___y_511_);
v_toCold_514_ = lean_ctor_get(v___y_510_, 0);
v_env_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_513_);
v_options_516_ = lean_ctor_get(v_toCold_514_, 2);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_518_ = lean_unsigned_to_nat(32u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
lean_dec_ref(v___x_519_);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_516_);
v___x_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_521_, 0, v_env_515_);
lean_ctor_set(v___x_521_, 1, v___x_517_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
lean_ctor_set(v___x_521_, 3, v_options_516_);
v___x_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_msgData_509_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msgData_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_ref_533_; lean_object* v___x_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_ref_533_ = lean_ctor_get(v___y_530_, 2);
v___x_534_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_529_, v___y_530_, v___y_531_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
lean_inc(v_ref_533_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_ref_533_);
lean_ctor_set(v___x_539_, 1, v_a_535_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 1);
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_549_, lean_object* v_msg_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_toCold_554_; lean_object* v_currRecDepth_555_; lean_object* v_ref_556_; uint16_t v_optionFlags_557_; uint8_t v_suppressElabErrors_558_; uint8_t v_isRecordingDeps_559_; lean_object* v_ref_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_toCold_554_ = lean_ctor_get(v___y_551_, 0);
v_currRecDepth_555_ = lean_ctor_get(v___y_551_, 1);
v_ref_556_ = lean_ctor_get(v___y_551_, 2);
v_optionFlags_557_ = lean_ctor_get_uint16(v___y_551_, sizeof(void*)*3);
v_suppressElabErrors_558_ = lean_ctor_get_uint8(v___y_551_, sizeof(void*)*3 + 2);
v_isRecordingDeps_559_ = lean_ctor_get_uint8(v___y_551_, sizeof(void*)*3 + 3);
v_ref_560_ = l_Lean_replaceRef(v_ref_549_, v_ref_556_);
lean_inc(v_currRecDepth_555_);
lean_inc_ref(v_toCold_554_);
v___x_561_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_561_, 0, v_toCold_554_);
lean_ctor_set(v___x_561_, 1, v_currRecDepth_555_);
lean_ctor_set(v___x_561_, 2, v_ref_560_);
lean_ctor_set_uint16(v___x_561_, sizeof(void*)*3, v_optionFlags_557_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3 + 2, v_suppressElabErrors_558_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3 + 3, v_isRecordingDeps_559_);
v___x_562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_550_, v___x_561_, v___y_552_);
lean_dec_ref_known(v___x_561_, 3);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_563_, v_msg_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v_ref_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_569_, lean_object* v_msg_570_, lean_object* v_declHint_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_570_, v_declHint_571_, v___y_572_, v___y_573_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_569_, v_a_576_, v___y_572_, v___y_573_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_578_, lean_object* v_msg_579_, lean_object* v_declHint_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_578_, v_msg_579_, v_declHint_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v_ref_578_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object* v_ref_591_, lean_object* v_constName_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_596_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1);
v___x_597_ = 0;
lean_inc(v_constName_592_);
v___x_598_ = l_Lean_MessageData_ofConstName(v_constName_592_, v___x_597_);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_591_, v___x_601_, v_constName_592_, v___y_593_, v___y_594_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_ref_603_, lean_object* v_constName_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_603_, v_constName_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_ref_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object* v_constName_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_ref_613_; lean_object* v___x_614_; 
v_ref_613_ = lean_ctor_get(v___y_610_, 2);
v___x_614_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_613_, v_constName_609_, v___y_610_, v___y_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_constName_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_constName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
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
v___x_628_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_620_, v___y_621_, v___y_622_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_constName_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_a_642_, lean_object* v_a_643_){
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_constName_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
lean_inc(v_constName_656_);
v___x_660_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_656_, v___y_657_, v___y_658_);
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
v___x_667_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_levelParams_665_, v___x_666_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_constName_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_constName_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_t_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_infoState_690_; uint8_t v_enabled_691_; 
v___x_689_ = lean_st_ref_get(v___y_687_);
v_infoState_690_ = lean_ctor_get(v___x_689_, 8);
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
lean_object* v___x_694_; lean_object* v_infoState_695_; lean_object* v_env_696_; lean_object* v_nextMacroScope_697_; lean_object* v_ngen_698_; lean_object* v_auxDeclNGen_699_; lean_object* v_traceState_700_; lean_object* v_cache_701_; lean_object* v_recordedDeps_702_; lean_object* v_messages_703_; lean_object* v_snapshotTasks_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_726_; 
v___x_694_ = lean_st_ref_take(v___y_687_);
v_infoState_695_ = lean_ctor_get(v___x_694_, 8);
v_env_696_ = lean_ctor_get(v___x_694_, 0);
v_nextMacroScope_697_ = lean_ctor_get(v___x_694_, 1);
v_ngen_698_ = lean_ctor_get(v___x_694_, 2);
v_auxDeclNGen_699_ = lean_ctor_get(v___x_694_, 3);
v_traceState_700_ = lean_ctor_get(v___x_694_, 4);
v_cache_701_ = lean_ctor_get(v___x_694_, 5);
v_recordedDeps_702_ = lean_ctor_get(v___x_694_, 6);
v_messages_703_ = lean_ctor_get(v___x_694_, 7);
v_snapshotTasks_704_ = lean_ctor_get(v___x_694_, 9);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_726_ == 0)
{
v___x_706_ = v___x_694_;
v_isShared_707_ = v_isSharedCheck_726_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snapshotTasks_704_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_703_);
lean_inc(v_recordedDeps_702_);
lean_inc(v_cache_701_);
lean_inc(v_traceState_700_);
lean_inc(v_auxDeclNGen_699_);
lean_inc(v_ngen_698_);
lean_inc(v_nextMacroScope_697_);
lean_inc(v_env_696_);
lean_dec(v___x_694_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_726_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
uint8_t v_enabled_708_; lean_object* v_assignment_709_; lean_object* v_lazyAssignment_710_; lean_object* v_trees_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_725_; 
v_enabled_708_ = lean_ctor_get_uint8(v_infoState_695_, sizeof(void*)*3);
v_assignment_709_ = lean_ctor_get(v_infoState_695_, 0);
v_lazyAssignment_710_ = lean_ctor_get(v_infoState_695_, 1);
v_trees_711_ = lean_ctor_get(v_infoState_695_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_infoState_695_);
if (v_isSharedCheck_725_ == 0)
{
v___x_713_ = v_infoState_695_;
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_trees_711_);
lean_inc(v_lazyAssignment_710_);
lean_inc(v_assignment_709_);
lean_dec(v_infoState_695_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_715_ = lean_box(0);
v___x_716_ = l_Lean_PersistentArray_push___redArg(v_trees_711_, v_t_686_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 2, v___x_716_);
v___x_718_ = v___x_713_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_assignment_709_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_lazyAssignment_710_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___x_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*3, v_enabled_708_);
v___x_718_ = v_reuseFailAlloc_724_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 8, v___x_718_);
v___x_720_ = v___x_706_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_env_696_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_nextMacroScope_697_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_ngen_698_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_auxDeclNGen_699_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_traceState_700_);
lean_ctor_set(v_reuseFailAlloc_723_, 5, v_cache_701_);
lean_ctor_set(v_reuseFailAlloc_723_, 6, v_recordedDeps_702_);
lean_ctor_set(v_reuseFailAlloc_723_, 7, v_messages_703_);
lean_ctor_set(v_reuseFailAlloc_723_, 8, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_723_, 9, v_snapshotTasks_704_);
v___x_720_ = v_reuseFailAlloc_723_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_st_ref_put(v___y_687_, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_715_);
return v___x_722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_727_, v___y_728_);
lean_dec(v___y_728_);
return v_res_730_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(32u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = ((size_t)5ULL);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_unsigned_to_nat(32u);
v___x_737_ = lean_mk_empty_array_with_capacity(v___x_736_);
v___x_738_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_739_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_735_);
lean_ctor_set(v___x_739_, 3, v___x_735_);
lean_ctor_set_usize(v___x_739_, 4, v___x_734_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_t_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_infoState_745_; uint8_t v_enabled_746_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_infoState_745_ = lean_ctor_get(v___x_744_, 8);
lean_inc_ref(v_infoState_745_);
lean_dec(v___x_744_);
v_enabled_746_ = lean_ctor_get_uint8(v_infoState_745_, sizeof(void*)*3);
lean_dec_ref(v_infoState_745_);
if (v_enabled_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v_t_740_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_t_740_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_750_, v___y_742_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_t_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v_t_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(lean_object* v_stx_757_, lean_object* v_n_758_, lean_object* v_expectedType_x3f_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_n_758_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_stx_757_);
v___x_767_ = l_Lean_LocalContext_empty;
v___x_768_ = 0;
v___x_769_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_769_, 0, v___x_766_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
lean_ctor_set(v___x_769_, 2, v_expectedType_x3f_759_);
lean_ctor_set(v___x_769_, 3, v_a_764_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*4, v___x_768_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*4 + 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
v___x_771_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_770_, v___y_760_, v___y_761_);
return v___x_771_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_expectedType_x3f_759_);
lean_dec(v_stx_757_);
v_a_772_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_763_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_763_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_780_, lean_object* v_n_781_, lean_object* v_expectedType_x3f_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v_stx_780_, v_n_781_, v_expectedType_x3f_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(lean_object* v_info_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_791_, 0, v_info_787_);
v___x_792_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_791_, v___y_788_, v___y_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0___boxed(lean_object* v_info_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v_info_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object* v_a_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v_key_801_; lean_object* v_value_802_; lean_object* v_tail_803_; uint8_t v___x_804_; 
v_key_801_ = lean_ctor_get(v_x_799_, 0);
v_value_802_ = lean_ctor_get(v_x_799_, 1);
v_tail_803_ = lean_ctor_get(v_x_799_, 2);
v___x_804_ = lean_name_eq(v_key_801_, v_a_798_);
if (v___x_804_ == 0)
{
v_x_799_ = v_tail_803_;
goto _start;
}
else
{
lean_object* v___x_806_; 
lean_inc(v_value_802_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_value_802_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_807_, lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_807_, v_x_808_);
lean_dec(v_x_808_);
lean_dec(v_a_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_buckets_812_; lean_object* v___x_813_; uint64_t v___y_815_; 
v_buckets_812_ = lean_ctor_get(v_m_810_, 1);
v___x_813_ = lean_array_get_size(v_buckets_812_);
if (lean_obj_tag(v_a_811_) == 0)
{
uint64_t v___x_829_; 
v___x_829_ = 1723ULL;
v___y_815_ = v___x_829_;
goto v___jp_814_;
}
else
{
uint64_t v_hash_830_; 
v_hash_830_ = lean_ctor_get_uint64(v_a_811_, sizeof(void*)*2);
v___y_815_ = v_hash_830_;
goto v___jp_814_;
}
v___jp_814_:
{
uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v_fold_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_816_ = 32ULL;
v___x_817_ = lean_uint64_shift_right(v___y_815_, v___x_816_);
v_fold_818_ = lean_uint64_xor(v___y_815_, v___x_817_);
v___x_819_ = 16ULL;
v___x_820_ = lean_uint64_shift_right(v_fold_818_, v___x_819_);
v___x_821_ = lean_uint64_xor(v_fold_818_, v___x_820_);
v___x_822_ = lean_uint64_to_usize(v___x_821_);
v___x_823_ = lean_usize_of_nat(v___x_813_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_sub(v___x_823_, v___x_824_);
v___x_826_ = lean_usize_land(v___x_822_, v___x_825_);
v___x_827_ = lean_array_uget_borrowed(v_buckets_812_, v___x_826_);
v___x_828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_811_, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_m_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_m_831_);
return v_res_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_keys_834_, lean_object* v_i_835_, lean_object* v_k_836_){
_start:
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_array_get_size(v_keys_834_);
v___x_838_ = lean_nat_dec_lt(v_i_835_, v___x_837_);
if (v___x_838_ == 0)
{
lean_dec(v_i_835_);
return v___x_838_;
}
else
{
lean_object* v_k_x27_839_; uint8_t v___x_840_; 
v_k_x27_839_ = lean_array_fget_borrowed(v_keys_834_, v_i_835_);
v___x_840_ = l_Lean_instBEqExtraModUse_beq(v_k_836_, v_k_x27_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_i_835_, v___x_841_);
lean_dec(v_i_835_);
v_i_835_ = v___x_842_;
goto _start;
}
else
{
lean_dec(v_i_835_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_keys_844_, lean_object* v_i_845_, lean_object* v_k_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_844_, v_i_845_, v_k_846_);
lean_dec_ref(v_k_846_);
lean_dec_ref(v_keys_844_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_849_, size_t v_x_850_, lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_es_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v_j_856_; lean_object* v___x_857_; 
v_es_852_ = lean_ctor_get(v_x_849_, 0);
v___x_853_ = lean_box(2);
v___x_854_ = ((size_t)31ULL);
v___x_855_ = lean_usize_land(v_x_850_, v___x_854_);
v_j_856_ = lean_usize_to_nat(v___x_855_);
v___x_857_ = lean_array_get_borrowed(v___x_853_, v_es_852_, v_j_856_);
lean_dec(v_j_856_);
switch(lean_obj_tag(v___x_857_))
{
case 0:
{
lean_object* v_key_858_; uint8_t v___x_859_; 
v_key_858_ = lean_ctor_get(v___x_857_, 0);
v___x_859_ = l_Lean_instBEqExtraModUse_beq(v_x_851_, v_key_858_);
return v___x_859_;
}
case 1:
{
lean_object* v_node_860_; size_t v___x_861_; size_t v___x_862_; 
v_node_860_ = lean_ctor_get(v___x_857_, 0);
v___x_861_ = ((size_t)5ULL);
v___x_862_ = lean_usize_shift_right(v_x_850_, v___x_861_);
v_x_849_ = v_node_860_;
v_x_850_ = v___x_862_;
goto _start;
}
default: 
{
uint8_t v___x_864_; 
v___x_864_ = 0;
return v___x_864_;
}
}
}
else
{
lean_object* v_ks_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_ks_865_ = lean_ctor_get(v_x_849_, 0);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_ks_865_, v___x_866_, v_x_851_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v_x_8204__boxed_871_; uint8_t v_res_872_; lean_object* v_r_873_; 
v_x_8204__boxed_871_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_872_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_868_, v_x_8204__boxed_871_, v_x_870_);
lean_dec_ref(v_x_870_);
lean_dec_ref(v_x_868_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
uint64_t v___x_876_; size_t v___x_877_; uint8_t v___x_878_; 
v___x_876_ = l_Lean_instHashableExtraModUse_hash(v_x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_874_, v___x_877_, v_x_875_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_879_, v_x_880_);
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_879_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_883_; double v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_float_of_nat(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_cls_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_ref_893_; lean_object* v___x_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_940_; 
v_ref_893_ = lean_ctor_get(v___y_890_, 2);
v___x_894_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_889_, v___y_890_, v___y_891_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_940_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_940_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_940_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v_traceState_900_; lean_object* v_env_901_; lean_object* v_nextMacroScope_902_; lean_object* v_ngen_903_; lean_object* v_auxDeclNGen_904_; lean_object* v_cache_905_; lean_object* v_recordedDeps_906_; lean_object* v_messages_907_; lean_object* v_infoState_908_; lean_object* v_snapshotTasks_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_939_; 
v___x_899_ = lean_st_ref_take(v___y_891_);
v_traceState_900_ = lean_ctor_get(v___x_899_, 4);
v_env_901_ = lean_ctor_get(v___x_899_, 0);
v_nextMacroScope_902_ = lean_ctor_get(v___x_899_, 1);
v_ngen_903_ = lean_ctor_get(v___x_899_, 2);
v_auxDeclNGen_904_ = lean_ctor_get(v___x_899_, 3);
v_cache_905_ = lean_ctor_get(v___x_899_, 5);
v_recordedDeps_906_ = lean_ctor_get(v___x_899_, 6);
v_messages_907_ = lean_ctor_get(v___x_899_, 7);
v_infoState_908_ = lean_ctor_get(v___x_899_, 8);
v_snapshotTasks_909_ = lean_ctor_get(v___x_899_, 9);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_939_ == 0)
{
v___x_911_ = v___x_899_;
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snapshotTasks_909_);
lean_inc(v_infoState_908_);
lean_inc(v_messages_907_);
lean_inc(v_recordedDeps_906_);
lean_inc(v_cache_905_);
lean_inc(v_traceState_900_);
lean_inc(v_auxDeclNGen_904_);
lean_inc(v_ngen_903_);
lean_inc(v_nextMacroScope_902_);
lean_inc(v_env_901_);
lean_dec(v___x_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint64_t v_tid_913_; lean_object* v_traces_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_938_; 
v_tid_913_ = lean_ctor_get_uint64(v_traceState_900_, sizeof(void*)*1);
v_traces_914_ = lean_ctor_get(v_traceState_900_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_traceState_900_);
if (v_isSharedCheck_938_ == 0)
{
v___x_916_ = v_traceState_900_;
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_traces_914_);
lean_dec(v_traceState_900_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; double v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_box(0);
v___x_920_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_921_ = 0;
v___x_922_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_923_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_923_, 0, v_cls_888_);
lean_ctor_set(v___x_923_, 1, v___x_919_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set_float(v___x_923_, sizeof(void*)*3, v___x_920_);
lean_ctor_set_float(v___x_923_, sizeof(void*)*3 + 8, v___x_920_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*3 + 16, v___x_921_);
v___x_924_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_925_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v_a_895_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_inc(v_ref_893_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_ref_893_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_PersistentArray_push___redArg(v_traces_914_, v___x_926_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_927_);
v___x_929_ = v___x_916_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_927_);
lean_ctor_set_uint64(v_reuseFailAlloc_937_, sizeof(void*)*1, v_tid_913_);
v___x_929_ = v_reuseFailAlloc_937_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_929_);
v___x_931_ = v___x_911_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_env_901_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_nextMacroScope_902_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_ngen_903_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_auxDeclNGen_904_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_936_, 5, v_cache_905_);
lean_ctor_set(v_reuseFailAlloc_936_, 6, v_recordedDeps_906_);
lean_ctor_set(v_reuseFailAlloc_936_, 7, v_messages_907_);
lean_ctor_set(v_reuseFailAlloc_936_, 8, v_infoState_908_);
lean_ctor_set(v_reuseFailAlloc_936_, 9, v_snapshotTasks_909_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_st_ref_put(v___y_891_, v___x_931_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_918_);
v___x_934_ = v___x_897_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_918_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_cls_941_, lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_941_, v_msg_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_946_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v_cls_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_cls_966_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_967_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_968_ = l_Lean_Name_append(v___x_967_, v_cls_966_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_mod_979_, uint8_t v_isMeta_980_, lean_object* v_hint_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_env_987_; uint8_t v_isExporting_988_; lean_object* v_entry_989_; lean_object* v___x_990_; lean_object* v_env_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___y_996_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_985_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0);
v___x_986_ = lean_st_ref_get(v___y_983_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v_isExporting_988_ = lean_ctor_get_uint8(v_env_987_, sizeof(void*)*8);
lean_dec_ref(v_env_987_);
lean_inc(v_mod_979_);
v_entry_989_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_989_, 0, v_mod_979_);
lean_ctor_set_uint8(v_entry_989_, sizeof(void*)*1, v_isExporting_988_);
lean_ctor_set_uint8(v_entry_989_, sizeof(void*)*1 + 1, v_isMeta_980_);
v___x_990_ = lean_st_ref_get(v___y_983_);
v_env_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_990_);
v___x_992_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_993_ = lean_box(1);
v___x_994_ = lean_box(0);
v___x_1022_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_985_, v___x_992_, v_env_991_, v___x_993_, v___x_994_);
v___x_1023_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v___x_1022_, v_entry_989_);
lean_dec(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v_toCold_1024_; lean_object* v_options_1025_; uint8_t v_hasTrace_1026_; 
v_toCold_1024_ = lean_ctor_get(v___y_982_, 0);
v_options_1025_ = lean_ctor_get(v_toCold_1024_, 2);
v_hasTrace_1026_ = lean_ctor_get_uint8(v_options_1025_, sizeof(void*)*1);
if (v_hasTrace_1026_ == 0)
{
lean_dec(v_hint_981_);
lean_dec(v_mod_979_);
v___y_996_ = v___y_983_;
goto v___jp_995_;
}
else
{
lean_object* v_inheritedTraceOptions_1027_; lean_object* v_cls_1028_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_inheritedTraceOptions_1027_ = lean_ctor_get(v_toCold_1024_, 11);
v_cls_1028_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_1048_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12);
v___x_1049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1027_, v_options_1025_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec(v_hint_981_);
lean_dec(v_mod_979_);
v___y_996_ = v___y_983_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1050_; lean_object* v___y_1052_; 
v___x_1050_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14);
if (v_isExporting_988_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19));
v___y_1052_ = v___x_1059_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20));
v___y_1052_ = v___x_1060_;
goto v___jp_1051_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_inc_ref(v___y_1052_);
v___x_1053_ = l_Lean_stringToMessageData(v___y_1052_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1050_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
if (v_isMeta_980_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17));
v___y_1035_ = v___x_1056_;
v___y_1036_ = v___x_1057_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18));
v___y_1035_ = v___x_1056_;
v___y_1036_ = v___x_1058_;
goto v___jp_1034_;
}
}
}
v___jp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___y_1030_);
lean_ctor_set(v___x_1032_, 1, v___y_1031_);
v___x_1033_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_1028_, v___x_1032_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_dec_ref_known(v___x_1033_, 1);
v___y_996_ = v___y_983_;
goto v___jp_995_;
}
else
{
lean_dec_ref_known(v_entry_989_, 1);
return v___x_1033_;
}
}
v___jp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc_ref(v___y_1036_);
v___x_1037_ = l_Lean_stringToMessageData(v___y_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___y_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_MessageData_ofName(v_mod_979_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_Name_isAnonymous(v_hint_981_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8);
v___x_1045_ = l_Lean_MessageData_ofName(v_hint_981_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___y_1030_ = v___x_1042_;
v___y_1031_ = v___x_1046_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_hint_981_);
v___x_1047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9);
v___y_1030_ = v___x_1042_;
v___y_1031_ = v___x_1047_;
goto v___jp_1029_;
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v_entry_989_, 1);
lean_dec(v_hint_981_);
lean_dec(v_mod_979_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v_toEnvExtension_998_; lean_object* v_env_999_; lean_object* v_nextMacroScope_1000_; lean_object* v_ngen_1001_; lean_object* v_auxDeclNGen_1002_; lean_object* v_traceState_1003_; lean_object* v_recordedDeps_1004_; lean_object* v_messages_1005_; lean_object* v_infoState_1006_; lean_object* v_snapshotTasks_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1020_; 
v___x_997_ = lean_st_ref_take(v___y_996_);
v_toEnvExtension_998_ = lean_ctor_get(v___x_992_, 0);
v_env_999_ = lean_ctor_get(v___x_997_, 0);
v_nextMacroScope_1000_ = lean_ctor_get(v___x_997_, 1);
v_ngen_1001_ = lean_ctor_get(v___x_997_, 2);
v_auxDeclNGen_1002_ = lean_ctor_get(v___x_997_, 3);
v_traceState_1003_ = lean_ctor_get(v___x_997_, 4);
v_recordedDeps_1004_ = lean_ctor_get(v___x_997_, 6);
v_messages_1005_ = lean_ctor_get(v___x_997_, 7);
v_infoState_1006_ = lean_ctor_get(v___x_997_, 8);
v_snapshotTasks_1007_ = lean_ctor_get(v___x_997_, 9);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_997_, 5);
lean_dec(v_unused_1021_);
v___x_1009_ = v___x_997_;
v_isShared_1010_ = v_isSharedCheck_1020_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snapshotTasks_1007_);
lean_inc(v_infoState_1006_);
lean_inc(v_messages_1005_);
lean_inc(v_recordedDeps_1004_);
lean_inc(v_traceState_1003_);
lean_inc(v_auxDeclNGen_1002_);
lean_inc(v_ngen_1001_);
lean_inc(v_nextMacroScope_1000_);
lean_inc(v_env_999_);
lean_dec(v___x_997_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1020_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_asyncMode_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v_asyncMode_1011_ = lean_ctor_get(v_toEnvExtension_998_, 2);
v___x_1012_ = lean_box(0);
v___x_1013_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_992_, v_env_999_, v_entry_989_, v_asyncMode_1011_, v___x_994_);
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 5, v___x_1014_);
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_nextMacroScope_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_ngen_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_auxDeclNGen_1002_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_traceState_1003_);
lean_ctor_set(v_reuseFailAlloc_1019_, 5, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 6, v_recordedDeps_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 7, v_messages_1005_);
lean_ctor_set(v_reuseFailAlloc_1019_, 8, v_infoState_1006_);
lean_ctor_set(v_reuseFailAlloc_1019_, 9, v_snapshotTasks_1007_);
v___x_1016_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_st_ref_put(v___y_996_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1012_);
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_mod_1063_, lean_object* v_isMeta_1064_, lean_object* v_hint_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v_isMeta_boxed_1069_; lean_object* v_res_1070_; 
v_isMeta_boxed_1069_ = lean_unbox(v_isMeta_1064_);
v_res_1070_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_mod_1063_, v_isMeta_boxed_1069_, v_hint_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object* v___x_1071_, lean_object* v_declName_1072_, lean_object* v_as_1073_, size_t v_sz_1074_, size_t v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_lt(v_i_1075_, v_sz_1074_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_declName_1072_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_b_1076_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v_modules_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v_toImport_1087_; lean_object* v_module_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1082_ = l_Lean_Environment_header(v___x_1071_);
v_modules_1083_ = lean_ctor_get(v___x_1082_, 3);
lean_inc_ref(v_modules_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1085_ = lean_array_uget_borrowed(v_as_1073_, v_i_1075_);
v___x_1086_ = lean_array_get(v___x_1084_, v_modules_1083_, v_a_1085_);
lean_dec_ref(v_modules_1083_);
v_toImport_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_toImport_1087_);
lean_dec(v___x_1086_);
v_module_1088_ = lean_ctor_get(v_toImport_1087_, 0);
lean_inc(v_module_1088_);
lean_dec_ref(v_toImport_1087_);
v___x_1089_ = lean_box(0);
v___x_1090_ = 0;
lean_inc(v_declName_1072_);
v___x_1091_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1088_, v___x_1090_, v_declName_1072_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1091_) == 0)
{
size_t v___x_1092_; size_t v___x_1093_; 
lean_dec_ref_known(v___x_1091_, 1);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_add(v_i_1075_, v___x_1092_);
v_i_1075_ = v___x_1093_;
v_b_1076_ = v___x_1089_;
goto _start;
}
else
{
lean_dec(v_declName_1072_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v___x_1095_, lean_object* v_declName_1096_, lean_object* v_as_1097_, lean_object* v_sz_1098_, lean_object* v_i_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1098_);
lean_dec(v_sz_1098_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v___x_1095_, v_declName_1096_, v_as_1097_, v_sz_boxed_1104_, v_i_boxed_1105_, v_b_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_as_1097_);
lean_dec_ref(v___x_1095_);
return v_res_1106_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(lean_object* v_declName_1110_, uint8_t v_isMeta_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_env_1120_; lean_object* v___y_1122_; lean_object* v___x_1135_; 
v___x_1115_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0);
v___x_1116_ = lean_st_ref_get(v___y_1113_);
v_env_1120_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_env_1120_);
lean_dec(v___x_1116_);
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1120_, v_declName_1110_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref(v_env_1120_);
lean_dec(v_declName_1110_);
goto v___jp_1117_;
}
else
{
lean_object* v_val_1136_; lean_object* v___x_1137_; lean_object* v_modules_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_val_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l_Lean_Environment_header(v_env_1120_);
v_modules_1138_ = lean_ctor_get(v___x_1137_, 3);
lean_inc_ref(v_modules_1138_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = lean_array_get_size(v_modules_1138_);
v___x_1140_ = lean_nat_dec_lt(v_val_1136_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_dec_ref(v_modules_1138_);
lean_dec(v_val_1136_);
lean_dec_ref(v_env_1120_);
lean_dec(v_declName_1110_);
goto v___jp_1117_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___y_1144_; 
v___x_1141_ = lean_array_fget(v_modules_1138_, v_val_1136_);
lean_dec(v_val_1136_);
lean_dec_ref(v_modules_1138_);
v___x_1142_ = lean_st_ref_get(v___y_1113_);
if (v_isMeta_1111_ == 0)
{
lean_dec(v___x_1142_);
v___y_1144_ = v_isMeta_1111_;
goto v___jp_1143_;
}
else
{
lean_object* v_env_1155_; uint8_t v___x_1156_; 
v_env_1155_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_env_1155_);
lean_dec(v___x_1142_);
lean_inc(v_declName_1110_);
v___x_1156_ = l_Lean_isMarkedMeta(v_env_1155_, v_declName_1110_);
if (v___x_1156_ == 0)
{
v___y_1144_ = v_isMeta_1111_;
goto v___jp_1143_;
}
else
{
uint8_t v___x_1157_; 
v___x_1157_ = 0;
v___y_1144_ = v___x_1157_;
goto v___jp_1143_;
}
}
v___jp_1143_:
{
lean_object* v_toImport_1145_; lean_object* v_module_1146_; lean_object* v___x_1147_; 
v_toImport_1145_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_toImport_1145_);
lean_dec(v___x_1141_);
v_module_1146_ = lean_ctor_get(v_toImport_1145_, 0);
lean_inc(v_module_1146_);
lean_dec_ref(v_toImport_1145_);
lean_inc(v_declName_1110_);
v___x_1147_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1146_, v___y_1144_, v_declName_1110_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref_known(v___x_1147_, 1);
v___x_1148_ = l_Lean_indirectModUseExt;
v___x_1149_ = lean_box(1);
v___x_1150_ = lean_box(0);
lean_inc_ref(v_env_1120_);
v___x_1151_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1115_, v___x_1148_, v_env_1120_, v___x_1149_, v___x_1150_);
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v___x_1151_, v_declName_1110_);
lean_dec(v___x_1151_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1));
v___y_1122_ = v___x_1153_;
goto v___jp_1121_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v___x_1152_, 1);
v___y_1122_ = v_val_1154_;
goto v___jp_1121_;
}
}
else
{
lean_dec_ref(v_env_1120_);
lean_dec(v_declName_1110_);
return v___x_1147_;
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
v___jp_1121_:
{
lean_object* v___x_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_box(0);
v_sz_1124_ = lean_array_size(v___y_1122_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v_env_1120_, v_declName_1110_, v___y_1122_, v_sz_1124_, v___x_1125_, v___x_1123_, v___y_1112_, v___y_1113_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v_env_1120_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1126_, 0);
lean_dec(v_unused_1134_);
v___x_1128_ = v___x_1126_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v___x_1126_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1123_);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1123_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1158_, lean_object* v_isMeta_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v_isMeta_boxed_1163_; lean_object* v_res_1164_; 
v_isMeta_boxed_1163_ = lean_unbox(v_isMeta_1159_);
v_res_1164_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_declName_1158_, v_isMeta_boxed_1163_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1164_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_box(1);
v___x_1174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_1175_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
lean_ctor_set(v___x_1176_, 2, v___x_1173_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_x_1177_, lean_object* v_stx_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1265_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1265_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1265_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_infoState_1189_; uint8_t v_enabled_1190_; 
v___x_1187_ = l_Lean_Syntax_getId(v_a_1183_);
v___x_1188_ = lean_st_ref_get(v___y_1180_);
v_infoState_1189_ = lean_ctor_get(v___x_1188_, 8);
lean_inc_ref(v_infoState_1189_);
lean_dec(v___x_1188_);
v_enabled_1190_ = lean_ctor_get_uint8(v_infoState_1189_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1189_);
if (v_enabled_1190_ == 0)
{
lean_object* v___x_1192_; 
lean_dec(v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1192_ = v___x_1185_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_Name_isAtomic(v___x_1187_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = l_Lean_Name_getRoot(v___x_1187_);
v___x_1196_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1197_ = lean_name_eq(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1199_ = v___x_1185_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1187_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___y_1204_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_del_object(v___x_1185_);
v___x_1201_ = lean_box(0);
lean_inc(v___x_1187_);
v___x_1202_ = l_Lean_Name_replacePrefix(v___x_1187_, v___x_1196_, v___x_1201_);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Lean_Syntax_identComponents(v_a_1183_, v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
v___y_1204_ = v___x_1260_;
goto v___jp_1203_;
}
else
{
lean_object* v_tail_1261_; 
v_tail_1261_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_tail_1261_);
lean_dec_ref_known(v___x_1260_, 2);
v___y_1204_ = v_tail_1261_;
goto v___jp_1203_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1205_ = lean_array_mk(v___y_1204_);
v___x_1206_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1207_ = lean_box(2);
v___x_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
lean_ctor_set(v___x_1208_, 2, v___x_1205_);
lean_inc_n(v___x_1202_, 2);
v___x_1209_ = l_Lean_mkIdentFrom(v___x_1208_, v___x_1202_, v_enabled_1190_);
lean_dec_ref_known(v___x_1208_, 3);
v___x_1210_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1211_ = lean_box(0);
lean_inc(v___x_1209_);
v___x_1212_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1212_, 0, v___x_1209_);
lean_ctor_set(v___x_1212_, 1, v___x_1202_);
lean_ctor_set(v___x_1212_, 2, v___x_1210_);
lean_ctor_set(v___x_1212_, 3, v___x_1211_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*4, v___x_1194_);
v___x_1213_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v___x_1212_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1213_, 0);
lean_dec(v_unused_1250_);
v___x_1215_ = v___x_1213_;
v_isShared_1216_ = v_isSharedCheck_1249_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v___x_1213_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1249_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v_env_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_st_ref_get(v___y_1180_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
lean_inc(v___x_1202_);
v___x_1219_ = l_Lean_Environment_contains(v_env_1218_, v___x_1202_, v_enabled_1190_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1221_; 
lean_dec(v___x_1209_);
lean_dec(v___x_1202_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1187_);
v___x_1221_ = v___x_1215_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1187_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
else
{
lean_object* v___x_1223_; 
lean_del_object(v___x_1215_);
lean_inc(v___x_1202_);
v___x_1223_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v___x_1202_, v___x_1194_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref_known(v___x_1223_, 1);
v___x_1224_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v___x_1209_, v___x_1202_, v___x_1211_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1232_);
v___x_1226_ = v___x_1224_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v___x_1224_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1187_);
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1187_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v___x_1187_);
v_a_1233_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1224_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1224_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v___x_1209_);
lean_dec(v___x_1202_);
lean_dec(v___x_1187_);
v_a_1241_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1223_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1223_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v___x_1209_);
lean_dec(v___x_1202_);
lean_dec(v___x_1187_);
v_a_1251_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1213_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1213_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1263_ = v___x_1185_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1187_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_a_1266_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1182_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1182_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_x_1274_, lean_object* v_stx_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_x_8747__boxed_1279_; lean_object* v_res_1280_; 
v_x_8747__boxed_1279_ = lean_unbox(v_x_1274_);
v_res_1280_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_x_8747__boxed_1279_, v_stx_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1314_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1315_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_t_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_1318_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_t_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_t_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1328_, lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_1329_, v_a_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_m_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1332_, v_m_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_m_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_1340_, v_x_1341_, v_x_1342_);
lean_dec_ref(v_x_1342_);
lean_dec_ref(v_x_1341_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_1346_, v_x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1349_, lean_object* v_a_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_00_u03b2_1349_, v_a_1350_, v_x_1351_);
lean_dec(v_x_1351_);
lean_dec(v_a_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1353_, lean_object* v_x_1354_, size_t v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_1354_, v_x_1355_, v_x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
size_t v_x_9082__boxed_1362_; uint8_t v_res_1363_; lean_object* v_r_1364_; 
v_x_9082__boxed_1362_ = lean_unbox_usize(v_x_1360_);
lean_dec(v_x_1360_);
v_res_1363_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1358_, v_x_1359_, v_x_9082__boxed_1362_, v_x_1361_);
lean_dec_ref(v_x_1361_);
lean_dec_ref(v_x_1359_);
v_r_1364_ = lean_box(v_res_1363_);
return v_r_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object* v_00_u03b1_1365_, lean_object* v_constName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_constName_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(v_00_u03b1_1371_, v_constName_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1376_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1377_, lean_object* v_keys_1378_, lean_object* v_vals_1379_, lean_object* v_heq_1380_, lean_object* v_i_1381_, lean_object* v_k_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_1378_, v_i_1381_, v_k_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_heq_1387_, lean_object* v_i_1388_, lean_object* v_k_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(v_00_u03b2_1384_, v_keys_1385_, v_vals_1386_, v_heq_1387_, v_i_1388_, v_k_1389_);
lean_dec_ref(v_k_1389_);
lean_dec_ref(v_vals_1386_);
lean_dec_ref(v_keys_1385_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object* v_00_u03b1_1392_, lean_object* v_ref_1393_, lean_object* v_constName_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_1393_, v_constName_1394_, v___y_1395_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_ref_1400_, lean_object* v_constName_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_1399_, v_ref_1400_, v_constName_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_ref_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_1407_, v_msg_1408_, v_declHint_1409_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v_declHint_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(v_00_u03b1_1414_, v_ref_1415_, v_msg_1416_, v_declHint_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v_ref_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1422_, lean_object* v_declHint_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1422_, v_declHint_1423_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1428_, lean_object* v_declHint_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(v_msg_1428_, v_declHint_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1434_, lean_object* v_ref_1435_, lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_1435_, v_msg_1436_, v___y_1437_, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1441_, lean_object* v_ref_1442_, lean_object* v_msg_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_1441_, v_ref_1442_, v_msg_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_ref_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1454_, v_msg_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1463_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1464_ = l_Lean_addBuiltinDocString(v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1494_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1495_ = l_Lean_addBuiltinDeclarationRanges(v___x_1493_, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1526_, uint8_t v___x_1527_, lean_object* v_id_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1526_, v___x_1527_);
v___x_1534_ = lean_string_append(v___x_1532_, v___x_1533_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1536_ = lean_string_append(v___x_1534_, v___x_1535_);
v___x_1537_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1528_, v___x_1536_, v___y_1530_, v___y_1531_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v_id_1540_, lean_object* v_x_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v___x_2296__boxed_1544_; lean_object* v_res_1545_; 
v___x_2296__boxed_1544_ = lean_unbox(v___x_1539_);
v_res_1545_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1538_, v___x_2296__boxed_1544_, v_id_1540_, v_x_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v_x_1541_);
lean_dec(v_id_1540_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1556_ = l_String_toRawSubstring_x27(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___y_1561_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1557_);
v___x_1581_ = l_Lean_Syntax_isOfKind(v_x_1557_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_x_1557_);
v___x_1582_ = lean_box(1);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1559_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v_id_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = lean_unsigned_to_nat(1u);
v_id_1585_ = l_Lean_Syntax_getArg(v_x_1557_, v___x_1584_);
lean_dec(v_x_1557_);
v___x_1586_ = l_Lean_TSyntax_getId(v_id_1585_);
lean_inc(v___x_1586_);
v___x_1587_ = l_Lean_Macro_resolveGlobalName(v___x_1586_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
if (lean_obj_tag(v_a_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1589_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1587_, 2);
v___x_1590_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1586_, v___x_1581_);
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
v___x_1595_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1585_, v___x_1594_, v_a_1558_, v_a_1589_);
lean_dec(v_id_1585_);
v___y_1561_ = v___x_1595_;
goto v___jp_1560_;
}
else
{
lean_object* v_head_1596_; lean_object* v_snd_1597_; 
v_head_1596_ = lean_ctor_get(v_a_1588_, 0);
v_snd_1597_ = lean_ctor_get(v_head_1596_, 1);
if (lean_obj_tag(v_snd_1597_) == 0)
{
lean_object* v_tail_1598_; 
v_tail_1598_ = lean_ctor_get(v_a_1588_, 1);
if (lean_obj_tag(v_tail_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1624_; 
lean_inc(v_head_1596_);
lean_dec_ref_known(v_a_1588_, 2);
lean_dec(v___x_1586_);
v_a_1599_ = lean_ctor_get(v___x_1587_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v___x_1587_, 0);
lean_dec(v_unused_1625_);
v___x_1601_ = v___x_1587_;
v_isShared_1602_ = v_isSharedCheck_1624_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1624_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_fst_1603_; lean_object* v_quotContext_1604_; lean_object* v_currMacroScope_1605_; lean_object* v_ref_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_fst_1603_ = lean_ctor_get(v_head_1596_, 0);
lean_inc(v_fst_1603_);
lean_dec(v_head_1596_);
v_quotContext_1604_ = lean_ctor_get(v_a_1558_, 1);
v_currMacroScope_1605_ = lean_ctor_get(v_a_1558_, 2);
v_ref_1606_ = lean_ctor_get(v_a_1558_, 5);
v___x_1607_ = 0;
v___x_1608_ = l_Lean_SourceInfo_fromRef(v_ref_1606_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1610_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1611_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1605_);
lean_inc(v_quotContext_1604_);
v___x_1612_ = l_Lean_addMacroScope(v_quotContext_1604_, v___x_1611_, v_currMacroScope_1605_);
v___x_1613_ = lean_box(0);
lean_inc_n(v___x_1608_, 2);
v___x_1614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1608_);
lean_ctor_set(v___x_1614_, 1, v___x_1610_);
lean_ctor_set(v___x_1614_, 2, v___x_1612_);
lean_ctor_set(v___x_1614_, 3, v___x_1613_);
v___x_1615_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1616_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1617_ = l_Lean_Name_append(v___x_1616_, v_fst_1603_);
v___x_1618_ = l_Lean_mkIdentFrom(v_id_1585_, v___x_1617_, v___x_1581_);
lean_dec(v_id_1585_);
v___x_1619_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1615_, v___x_1618_);
v___x_1620_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1609_, v___x_1614_, v___x_1619_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1620_);
v___x_1622_ = v___x_1601_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_a_1599_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1587_, 2);
v___x_1627_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1586_, v___x_1581_, v_id_1585_, v_a_1588_, v_a_1558_, v_a_1626_);
lean_dec_ref_known(v_a_1588_, 2);
lean_dec(v_id_1585_);
v___y_1561_ = v___x_1627_;
goto v___jp_1560_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1587_, 2);
v___x_1629_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1586_, v___x_1581_, v_id_1585_, v_a_1588_, v_a_1558_, v_a_1628_);
lean_dec_ref_known(v_a_1588_, 2);
lean_dec(v_id_1585_);
v___y_1561_ = v___x_1629_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v___x_1586_);
lean_dec(v_id_1585_);
v_a_1630_ = lean_ctor_get(v___x_1587_, 0);
v_a_1631_ = lean_ctor_get(v___x_1587_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1587_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_inc(v_a_1630_);
lean_dec(v___x_1587_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1630_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
v___jp_1560_:
{
if (lean_obj_tag(v___y_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_a_1562_ = lean_ctor_get(v___y_1561_, 0);
v_a_1563_ = lean_ctor_get(v___y_1561_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___y_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___y_1561_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_inc(v_a_1562_);
lean_dec(v___y_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_a_1571_ = lean_ctor_get(v___y_1561_, 0);
v_a_1572_ = lean_ctor_get(v___y_1561_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___y_1561_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___y_1561_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_inc(v_a_1571_);
lean_dec(v___y_1561_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1639_, v_a_1640_, v_a_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1643_){
_start:
{
lean_object* v_subExpr_1645_; lean_object* v_expr_1646_; lean_object* v___x_1647_; 
v_subExpr_1645_ = lean_ctor_get(v___y_1643_, 3);
v_expr_1646_ = lean_ctor_get(v_subExpr_1645_, 0);
lean_inc_ref(v_expr_1646_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_expr_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1648_);
lean_dec_ref(v___y_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1651_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1667_, lean_object* v_us_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1670_ = l_Lean_Name_append(v___x_1669_, v_c_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1671_, lean_object* v_us_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1671_, v_us_1672_);
lean_dec(v_us_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1679_);
lean_dec(v_x_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1791_; 
v___x_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1708_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1791_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1791_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
switch(lean_obj_tag(v_a_1716_))
{
case 0:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec_ref_known(v_a_1716_, 1);
v___x_1720_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
case 1:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec_ref_known(v_a_1716_, 1);
v___x_1724_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1724_);
v___x_1726_ = v___x_1718_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
case 2:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec_ref_known(v_a_1716_, 1);
v___x_1728_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1728_);
v___x_1730_ = v___x_1718_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
case 3:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec_ref_known(v_a_1716_, 1);
v___x_1732_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1732_);
v___x_1734_ = v___x_1718_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
case 4:
{
lean_object* v_declName_1736_; lean_object* v_us_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v_declName_1736_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_declName_1736_);
v_us_1737_ = lean_ctor_get(v_a_1716_, 1);
lean_inc(v_us_1737_);
lean_dec_ref_known(v_a_1716_, 2);
v___x_1738_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1736_, v_us_1737_);
lean_dec(v_us_1737_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1738_);
v___x_1740_ = v___x_1718_;
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
case 5:
{
lean_object* v_fn_1742_; lean_object* v___x_1743_; 
v_fn_1742_ = lean_ctor_get(v_a_1716_, 0);
lean_inc_ref(v_fn_1742_);
lean_dec_ref_known(v_a_1716_, 2);
v___x_1743_ = l_Lean_Expr_getAppFn(v_fn_1742_);
lean_dec_ref(v_fn_1742_);
if (lean_obj_tag(v___x_1743_) == 4)
{
lean_object* v_declName_1744_; lean_object* v_us_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v_declName_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_declName_1744_);
v_us_1745_ = lean_ctor_get(v___x_1743_, 1);
lean_inc(v_us_1745_);
lean_dec_ref_known(v___x_1743_, 2);
v___x_1746_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1744_, v_us_1745_);
lean_dec(v_us_1745_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1746_);
v___x_1748_ = v___x_1718_;
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
else
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec_ref(v___x_1743_);
v___x_1750_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1750_);
v___x_1752_ = v___x_1718_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
case 6:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec_ref_known(v_a_1716_, 3);
v___x_1754_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1754_);
v___x_1756_ = v___x_1718_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
case 7:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec_ref_known(v_a_1716_, 3);
v___x_1758_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1758_);
v___x_1760_ = v___x_1718_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
case 8:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec_ref_known(v_a_1716_, 4);
v___x_1762_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1762_);
v___x_1764_ = v___x_1718_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
case 9:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec_ref_known(v_a_1716_, 1);
v___x_1766_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1766_);
v___x_1768_ = v___x_1718_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
case 10:
{
lean_object* v_data_1770_; 
v_data_1770_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_data_1770_);
lean_dec_ref_known(v_a_1716_, 2);
if (lean_obj_tag(v_data_1770_) == 1)
{
lean_object* v_tail_1771_; 
v_tail_1771_ = lean_ctor_get(v_data_1770_, 1);
if (lean_obj_tag(v_tail_1771_) == 0)
{
lean_object* v_head_1772_; lean_object* v_fst_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v_head_1772_ = lean_ctor_get(v_data_1770_, 0);
lean_inc(v_head_1772_);
lean_dec_ref_known(v_data_1770_, 2);
v_fst_1773_ = lean_ctor_get(v_head_1772_, 0);
lean_inc(v_fst_1773_);
lean_dec(v_head_1772_);
v___x_1774_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1775_ = l_Lean_Name_append(v___x_1774_, v_fst_1773_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1775_);
v___x_1777_ = v___x_1718_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1770_);
lean_dec_ref_known(v_data_1770_, 2);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1779_);
v___x_1781_ = v___x_1718_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1770_);
lean_dec(v_data_1770_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1783_);
v___x_1785_ = v___x_1718_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
default: 
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec_ref_known(v_a_1716_, 3);
v___x_1787_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1787_);
v___x_1789_ = v___x_1718_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1800_, lean_object* v_k_1801_, lean_object* v_v_1802_){
_start:
{
lean_object* v_map_1803_; uint8_t v_hasTrace_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1817_; 
v_map_1803_ = lean_ctor_get(v_o_1800_, 0);
v_hasTrace_1804_ = lean_ctor_get_uint8(v_o_1800_, sizeof(void*)*1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_o_1800_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1806_ = v_o_1800_;
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_map_1803_);
lean_dec(v_o_1800_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; 
lean_inc(v_k_1801_);
v___x_1808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1801_, v_v_1802_, v_map_1803_);
if (v_hasTrace_1804_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1812_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_1810_ = l_Lean_Name_isPrefixOf(v___x_1809_, v_k_1801_);
lean_dec(v_k_1801_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1812_ = v___x_1806_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1808_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*1, v___x_1810_);
return v___x_1812_;
}
}
else
{
lean_object* v___x_1815_; 
lean_dec(v_k_1801_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1815_ = v___x_1806_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*1, v_hasTrace_1804_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1818_){
_start:
{
lean_object* v_subExpr_1820_; lean_object* v_pos_1821_; lean_object* v___x_1822_; 
v_subExpr_1820_ = lean_ctor_get(v___y_1818_, 3);
v_pos_1821_ = lean_ctor_get(v_subExpr_1820_, 1);
lean_inc(v_pos_1821_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_pos_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1823_);
lean_dec_ref(v___y_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1826_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1842_, lean_object* v_k_1843_){
_start:
{
if (lean_obj_tag(v_t_1842_) == 0)
{
lean_object* v_k_1844_; lean_object* v_v_1845_; lean_object* v_l_1846_; lean_object* v_r_1847_; uint8_t v___x_1848_; 
v_k_1844_ = lean_ctor_get(v_t_1842_, 1);
v_v_1845_ = lean_ctor_get(v_t_1842_, 2);
v_l_1846_ = lean_ctor_get(v_t_1842_, 3);
v_r_1847_ = lean_ctor_get(v_t_1842_, 4);
v___x_1848_ = lean_nat_dec_lt(v_k_1843_, v_k_1844_);
if (v___x_1848_ == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_eq(v_k_1843_, v_k_1844_);
if (v___x_1849_ == 0)
{
v_t_1842_ = v_r_1847_;
goto _start;
}
else
{
lean_object* v___x_1851_; 
lean_inc(v_v_1845_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_v_1845_);
return v___x_1851_;
}
}
else
{
v_t_1842_ = v_l_1846_;
goto _start;
}
}
else
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1854_, lean_object* v_k_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1854_, v_k_1855_);
lean_dec(v_k_1855_);
lean_dec(v_t_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1857_, lean_object* v_x_1858_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v_k_1860_; lean_object* v_v_1861_; lean_object* v_l_1862_; lean_object* v_r_1863_; lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_k_1860_ = lean_ctor_get(v_x_1858_, 1);
lean_inc(v_k_1860_);
v_v_1861_ = lean_ctor_get(v_x_1858_, 2);
lean_inc(v_v_1861_);
v_l_1862_ = lean_ctor_get(v_x_1858_, 3);
lean_inc(v_l_1862_);
v_r_1863_ = lean_ctor_get(v_x_1858_, 4);
lean_inc(v_r_1863_);
lean_dec_ref_known(v_x_1858_, 5);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1857_, v_l_1862_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v_a_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_a_1866_);
lean_dec(v_a_1865_);
v___x_1867_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1866_, v_k_1860_, v_v_1861_);
v_init_1857_ = v___x_1867_;
v_x_1858_ = v_r_1863_;
goto _start;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_init_1857_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1871_, lean_object* v_x_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1871_, v_x_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1905_; 
v___x_1882_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1879_);
v___x_1883_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1875_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1905_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1905_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_optionsPerPos_1888_; lean_object* v___x_1889_; 
v_optionsPerPos_1888_ = lean_ctor_get(v_a_1875_, 0);
v___x_1889_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1888_, v_a_1884_);
lean_dec(v_a_1884_);
if (lean_obj_tag(v___x_1889_) == 1)
{
lean_object* v_val_1890_; lean_object* v_map_1891_; lean_object* v___x_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1886_);
v_val_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_val_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v_map_1891_ = lean_ctor_get(v_val_1890_, 0);
lean_inc(v_map_1891_);
lean_dec(v_val_1890_);
v___x_1892_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v___x_1882_, v_map_1891_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_a_1897_; lean_object* v___x_1899_; 
v_a_1897_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_a_1897_);
lean_dec(v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_a_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_object* v___x_1903_; 
lean_dec(v___x_1889_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1882_);
v___x_1903_ = v___x_1886_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1882_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1914_, lean_object* v_t_1915_, lean_object* v_k_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1915_, v_k_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1918_, lean_object* v_t_1919_, lean_object* v_k_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1918_, v_t_1919_, v_k_1920_);
lean_dec(v_k_1920_);
lean_dec(v_t_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1922_, lean_object* v_x_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1922_, v_x_1923_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1932_, v_x_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_apply_1(v_opt_1942_, v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_opt_1942_);
v_a_1960_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1950_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1950_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_1977_, lean_object* v_opt_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_opt_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_1987_, v_opt_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_1997_, lean_object* v_d_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1997_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; uint8_t v___x_2008_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = lean_unbox(v_a_2007_);
lean_dec(v_a_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v_d_1998_);
v___x_2009_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; 
lean_inc(v_a_2004_);
lean_inc_ref(v_a_2003_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
v___x_2010_ = lean_apply_7(v_d_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, lean_box(0));
return v___x_2010_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_d_1998_);
v_a_2011_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2006_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2006_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2019_, lean_object* v_d_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2019_, v_d_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2029_, lean_object* v_d_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2029_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; uint8_t v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_inc(v_a_2036_);
lean_inc_ref(v_a_2035_);
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
lean_inc(v_a_2032_);
lean_inc_ref(v_a_2031_);
v___x_2041_ = lean_apply_7(v_d_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, lean_box(0));
return v___x_2041_;
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref(v_d_2030_);
v___x_2042_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2042_;
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_d_2030_);
v_a_2043_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2038_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2038_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2051_, lean_object* v_d_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2051_, v_d_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2061_, lean_object* v_v_2062_, lean_object* v_t_2063_){
_start:
{
if (lean_obj_tag(v_t_2063_) == 0)
{
lean_object* v_size_2064_; lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v_l_2067_; lean_object* v_r_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2349_; 
v_size_2064_ = lean_ctor_get(v_t_2063_, 0);
v_k_2065_ = lean_ctor_get(v_t_2063_, 1);
v_v_2066_ = lean_ctor_get(v_t_2063_, 2);
v_l_2067_ = lean_ctor_get(v_t_2063_, 3);
v_r_2068_ = lean_ctor_get(v_t_2063_, 4);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_t_2063_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2070_ = v_t_2063_;
v_isShared_2071_ = v_isSharedCheck_2349_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_r_2068_);
lean_inc(v_l_2067_);
lean_inc(v_v_2066_);
lean_inc(v_k_2065_);
lean_inc(v_size_2064_);
lean_dec(v_t_2063_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2349_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_lt(v_k_2061_, v_k_2065_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_nat_dec_eq(v_k_2061_, v_k_2065_);
if (v___x_2073_ == 0)
{
lean_object* v_impl_2074_; lean_object* v___x_2075_; 
lean_dec(v_size_2064_);
v_impl_2074_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2061_, v_v_2062_, v_r_2068_);
v___x_2075_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2067_) == 0)
{
lean_object* v_size_2076_; lean_object* v_size_2077_; lean_object* v_k_2078_; lean_object* v_v_2079_; lean_object* v_l_2080_; lean_object* v_r_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_size_2076_ = lean_ctor_get(v_l_2067_, 0);
v_size_2077_ = lean_ctor_get(v_impl_2074_, 0);
lean_inc(v_size_2077_);
v_k_2078_ = lean_ctor_get(v_impl_2074_, 1);
lean_inc(v_k_2078_);
v_v_2079_ = lean_ctor_get(v_impl_2074_, 2);
lean_inc(v_v_2079_);
v_l_2080_ = lean_ctor_get(v_impl_2074_, 3);
lean_inc(v_l_2080_);
v_r_2081_ = lean_ctor_get(v_impl_2074_, 4);
lean_inc(v_r_2081_);
v___x_2082_ = lean_unsigned_to_nat(3u);
v___x_2083_ = lean_nat_mul(v___x_2082_, v_size_2076_);
v___x_2084_ = lean_nat_dec_lt(v___x_2083_, v_size_2077_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec(v_r_2081_);
lean_dec(v_l_2080_);
lean_dec(v_v_2079_);
lean_dec(v_k_2078_);
v___x_2085_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2086_ = lean_nat_add(v___x_2085_, v_size_2077_);
lean_dec(v_size_2077_);
lean_dec(v___x_2085_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_impl_2074_);
lean_ctor_set(v___x_2070_, 0, v___x_2086_);
v___x_2088_ = v___x_2070_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_impl_2074_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
else
{
lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2153_; 
v_isSharedCheck_2153_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2154_ = lean_ctor_get(v_impl_2074_, 4);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_impl_2074_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_impl_2074_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2158_);
v___x_2091_ = v_impl_2074_;
v_isShared_2092_ = v_isSharedCheck_2153_;
goto v_resetjp_2090_;
}
else
{
lean_dec(v_impl_2074_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2153_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_size_2093_; lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v_l_2096_; lean_object* v_r_2097_; lean_object* v_size_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_size_2093_ = lean_ctor_get(v_l_2080_, 0);
v_k_2094_ = lean_ctor_get(v_l_2080_, 1);
v_v_2095_ = lean_ctor_get(v_l_2080_, 2);
v_l_2096_ = lean_ctor_get(v_l_2080_, 3);
v_r_2097_ = lean_ctor_get(v_l_2080_, 4);
v_size_2098_ = lean_ctor_get(v_r_2081_, 0);
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = lean_nat_mul(v___x_2099_, v_size_2098_);
v___x_2101_ = lean_nat_dec_lt(v_size_2093_, v___x_2100_);
lean_dec(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2129_; 
lean_inc(v_r_2097_);
lean_inc(v_l_2096_);
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_l_2080_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; lean_object* v_unused_2134_; 
v_unused_2130_ = lean_ctor_get(v_l_2080_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2080_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2080_, 2);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_l_2080_, 1);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_l_2080_, 0);
lean_dec(v_unused_2134_);
v___x_2103_ = v_l_2080_;
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_l_2080_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2119_; 
v___x_2105_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2106_ = lean_nat_add(v___x_2105_, v_size_2077_);
lean_dec(v_size_2077_);
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2127_; 
v_size_2127_ = lean_ctor_get(v_l_2096_, 0);
lean_inc(v_size_2127_);
v___y_2119_ = v_size_2127_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_unsigned_to_nat(0u);
v___y_2119_ = v___x_2128_;
goto v___jp_2118_;
}
v___jp_2107_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_nat_add(v___y_2108_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec(v___y_2108_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_r_2081_);
lean_ctor_set(v___x_2103_, 3, v_r_2097_);
lean_ctor_set(v___x_2103_, 2, v_v_2079_);
lean_ctor_set(v___x_2103_, 1, v_k_2078_);
lean_ctor_set(v___x_2103_, 0, v___x_2111_);
v___x_2113_ = v___x_2103_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_r_2097_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_r_2081_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v___x_2113_);
lean_ctor_set(v___x_2091_, 3, v___y_2109_);
lean_ctor_set(v___x_2091_, 2, v_v_2095_);
lean_ctor_set(v___x_2091_, 1, v_k_2094_);
lean_ctor_set(v___x_2091_, 0, v___x_2106_);
v___x_2115_ = v___x_2091_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v___y_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_nat_add(v___x_2105_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec(v___x_2105_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_l_2096_);
lean_ctor_set(v___x_2070_, 0, v___x_2120_);
v___x_2122_ = v___x_2070_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_l_2096_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_nat_add(v___x_2075_, v_size_2098_);
if (lean_obj_tag(v_r_2097_) == 0)
{
lean_object* v_size_2124_; 
v_size_2124_ = lean_ctor_get(v_r_2097_, 0);
lean_inc(v_size_2124_);
v___y_2108_ = v___x_2123_;
v___y_2109_ = v___x_2122_;
v___y_2110_ = v_size_2124_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___y_2108_ = v___x_2123_;
v___y_2109_ = v___x_2122_;
v___y_2110_ = v___x_2125_;
goto v___jp_2107_;
}
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_del_object(v___x_2070_);
v___x_2135_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2077_);
lean_dec(v_size_2077_);
v___x_2137_ = lean_nat_add(v___x_2135_, v_size_2093_);
lean_dec(v___x_2135_);
lean_inc_ref(v_l_2067_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v_l_2080_);
lean_ctor_set(v___x_2091_, 3, v_l_2067_);
lean_ctor_set(v___x_2091_, 2, v_v_2066_);
lean_ctor_set(v___x_2091_, 1, v_k_2065_);
lean_ctor_set(v___x_2091_, 0, v___x_2137_);
v___x_2139_ = v___x_2091_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_l_2080_);
v___x_2139_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v_l_2067_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2147_ = lean_ctor_get(v_l_2067_, 4);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2067_, 3);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2067_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2067_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_l_2067_, 0);
lean_dec(v_unused_2151_);
v___x_2141_ = v_l_2067_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_l_2067_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_r_2081_);
lean_ctor_set(v___x_2141_, 3, v___x_2139_);
lean_ctor_set(v___x_2141_, 2, v_v_2079_);
lean_ctor_set(v___x_2141_, 1, v_k_2078_);
lean_ctor_set(v___x_2141_, 0, v___x_2136_);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_2081_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2159_; 
v_l_2159_ = lean_ctor_get(v_impl_2074_, 3);
lean_inc(v_l_2159_);
if (lean_obj_tag(v_l_2159_) == 0)
{
lean_object* v_r_2160_; lean_object* v_k_2161_; lean_object* v_v_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2185_; 
v_r_2160_ = lean_ctor_get(v_impl_2074_, 4);
v_k_2161_ = lean_ctor_get(v_impl_2074_, 1);
v_v_2162_ = lean_ctor_get(v_impl_2074_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2186_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2187_);
v___x_2164_ = v_impl_2074_;
v_isShared_2165_ = v_isSharedCheck_2185_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_r_2160_);
lean_inc(v_v_2162_);
lean_inc(v_k_2161_);
lean_dec(v_impl_2074_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2185_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_k_2166_; lean_object* v_v_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2181_; 
v_k_2166_ = lean_ctor_get(v_l_2159_, 1);
v_v_2167_ = lean_ctor_get(v_l_2159_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_l_2159_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2182_ = lean_ctor_get(v_l_2159_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2159_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2159_, 0);
lean_dec(v_unused_2184_);
v___x_2169_ = v_l_2159_;
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
lean_dec(v_l_2159_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2160_, 2);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 4, v_r_2160_);
lean_ctor_set(v___x_2169_, 3, v_r_2160_);
lean_ctor_set(v___x_2169_, 2, v_v_2066_);
lean_ctor_set(v___x_2169_, 1, v_k_2065_);
lean_ctor_set(v___x_2169_, 0, v___x_2075_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_r_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_r_2160_);
v___x_2173_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
lean_inc(v_r_2160_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 3, v_r_2160_);
lean_ctor_set(v___x_2164_, 0, v___x_2075_);
v___x_2175_ = v___x_2164_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2161_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2162_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_r_2160_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_r_2160_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2175_);
lean_ctor_set(v___x_2070_, 3, v___x_2173_);
lean_ctor_set(v___x_2070_, 2, v_v_2167_);
lean_ctor_set(v___x_2070_, 1, v_k_2166_);
lean_ctor_set(v___x_2070_, 0, v___x_2171_);
v___x_2177_ = v___x_2070_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v___x_2175_);
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
}
else
{
lean_object* v_r_2188_; 
v_r_2188_ = lean_ctor_get(v_impl_2074_, 4);
lean_inc(v_r_2188_);
if (lean_obj_tag(v_r_2188_) == 0)
{
lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2201_; 
v_k_2189_ = lean_ctor_get(v_impl_2074_, 1);
v_v_2190_ = lean_ctor_get(v_impl_2074_, 2);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2202_ = lean_ctor_get(v_impl_2074_, 4);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2204_);
v___x_2192_ = v_impl_2074_;
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
lean_dec(v_impl_2074_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 4, v_l_2159_);
lean_ctor_set(v___x_2192_, 2, v_v_2066_);
lean_ctor_set(v___x_2192_, 1, v_k_2065_);
lean_ctor_set(v___x_2192_, 0, v___x_2075_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_l_2159_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_r_2188_);
lean_ctor_set(v___x_2070_, 3, v___x_2196_);
lean_ctor_set(v___x_2070_, 2, v_v_2190_);
lean_ctor_set(v___x_2070_, 1, v_k_2189_);
lean_ctor_set(v___x_2070_, 0, v___x_2194_);
v___x_2198_ = v___x_2070_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2189_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2190_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_r_2188_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(2u);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_impl_2074_);
lean_ctor_set(v___x_2070_, 3, v_r_2188_);
lean_ctor_set(v___x_2070_, 0, v___x_2205_);
v___x_2207_ = v___x_2070_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_r_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_impl_2074_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v___x_2210_; 
lean_dec(v_v_2066_);
lean_dec(v_k_2065_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 2, v_v_2062_);
lean_ctor_set(v___x_2070_, 1, v_k_2061_);
v___x_2210_ = v___x_2070_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_size_2064_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_2061_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_2062_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_r_2068_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_impl_2212_; lean_object* v___x_2213_; 
lean_dec(v_size_2064_);
v_impl_2212_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2061_, v_v_2062_, v_l_2067_);
v___x_2213_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2068_) == 0)
{
lean_object* v_size_2214_; lean_object* v_size_2215_; lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v_l_2218_; lean_object* v_r_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_size_2214_ = lean_ctor_get(v_r_2068_, 0);
v_size_2215_ = lean_ctor_get(v_impl_2212_, 0);
lean_inc(v_size_2215_);
v_k_2216_ = lean_ctor_get(v_impl_2212_, 1);
lean_inc(v_k_2216_);
v_v_2217_ = lean_ctor_get(v_impl_2212_, 2);
lean_inc(v_v_2217_);
v_l_2218_ = lean_ctor_get(v_impl_2212_, 3);
lean_inc(v_l_2218_);
v_r_2219_ = lean_ctor_get(v_impl_2212_, 4);
lean_inc(v_r_2219_);
v___x_2220_ = lean_unsigned_to_nat(3u);
v___x_2221_ = lean_nat_mul(v___x_2220_, v_size_2214_);
v___x_2222_ = lean_nat_dec_lt(v___x_2221_, v_size_2215_);
lean_dec(v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_dec(v_r_2219_);
lean_dec(v_l_2218_);
lean_dec(v_v_2217_);
lean_dec(v_k_2216_);
v___x_2223_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2224_ = lean_nat_add(v___x_2223_, v_size_2214_);
lean_dec(v___x_2223_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 3, v_impl_2212_);
lean_ctor_set(v___x_2070_, 0, v___x_2224_);
v___x_2226_ = v___x_2070_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_impl_2212_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_r_2068_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2293_; 
v_isSharedCheck_2293_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; 
v_unused_2294_ = lean_ctor_get(v_impl_2212_, 4);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2212_, 2);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_impl_2212_, 1);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2298_);
v___x_2229_ = v_impl_2212_;
v_isShared_2230_ = v_isSharedCheck_2293_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v_impl_2212_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2293_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_size_2231_; lean_object* v_size_2232_; lean_object* v_k_2233_; lean_object* v_v_2234_; lean_object* v_l_2235_; lean_object* v_r_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_size_2231_ = lean_ctor_get(v_l_2218_, 0);
v_size_2232_ = lean_ctor_get(v_r_2219_, 0);
v_k_2233_ = lean_ctor_get(v_r_2219_, 1);
v_v_2234_ = lean_ctor_get(v_r_2219_, 2);
v_l_2235_ = lean_ctor_get(v_r_2219_, 3);
v_r_2236_ = lean_ctor_get(v_r_2219_, 4);
v___x_2237_ = lean_unsigned_to_nat(2u);
v___x_2238_ = lean_nat_mul(v___x_2237_, v_size_2231_);
v___x_2239_ = lean_nat_dec_lt(v_size_2232_, v___x_2238_);
lean_dec(v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2268_; 
lean_inc(v_r_2236_);
lean_inc(v_l_2235_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_r_2219_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; lean_object* v_unused_2272_; lean_object* v_unused_2273_; 
v_unused_2269_ = lean_ctor_get(v_r_2219_, 4);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2219_, 3);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_r_2219_, 2);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_r_2219_, 1);
lean_dec(v_unused_2272_);
v_unused_2273_ = lean_ctor_get(v_r_2219_, 0);
lean_dec(v_unused_2273_);
v___x_2241_ = v_r_2219_;
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v_r_2219_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___x_2256_; lean_object* v___y_2258_; 
v___x_2243_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2244_ = lean_nat_add(v___x_2243_, v_size_2214_);
lean_dec(v___x_2243_);
v___x_2256_ = lean_nat_add(v___x_2213_, v_size_2231_);
if (lean_obj_tag(v_l_2235_) == 0)
{
lean_object* v_size_2266_; 
v_size_2266_ = lean_ctor_get(v_l_2235_, 0);
lean_inc(v_size_2266_);
v___y_2258_ = v_size_2266_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___y_2258_ = v___x_2267_;
goto v___jp_2257_;
}
v___jp_2245_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_nat_add(v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v_r_2068_);
lean_ctor_set(v___x_2241_, 3, v_r_2236_);
lean_ctor_set(v___x_2241_, 2, v_v_2066_);
lean_ctor_set(v___x_2241_, 1, v_k_2065_);
lean_ctor_set(v___x_2241_, 0, v___x_2249_);
v___x_2251_ = v___x_2241_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_r_2068_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v___x_2251_);
lean_ctor_set(v___x_2229_, 3, v___y_2246_);
lean_ctor_set(v___x_2229_, 2, v_v_2234_);
lean_ctor_set(v___x_2229_, 1, v_k_2233_);
lean_ctor_set(v___x_2229_, 0, v___x_2244_);
v___x_2253_ = v___x_2229_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v___y_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
v___jp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_nat_add(v___x_2256_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec(v___x_2256_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_l_2235_);
lean_ctor_set(v___x_2070_, 3, v_l_2218_);
lean_ctor_set(v___x_2070_, 2, v_v_2217_);
lean_ctor_set(v___x_2070_, 1, v_k_2216_);
lean_ctor_set(v___x_2070_, 0, v___x_2259_);
v___x_2261_ = v___x_2070_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_l_2218_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_l_2235_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_nat_add(v___x_2213_, v_size_2214_);
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_size_2263_; 
v_size_2263_ = lean_ctor_get(v_r_2236_, 0);
lean_inc(v_size_2263_);
v___y_2246_ = v___x_2261_;
v___y_2247_ = v___x_2262_;
v___y_2248_ = v_size_2263_;
goto v___jp_2245_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___y_2246_ = v___x_2261_;
v___y_2247_ = v___x_2262_;
v___y_2248_ = v___x_2264_;
goto v___jp_2245_;
}
}
}
}
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_del_object(v___x_2070_);
v___x_2274_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2275_ = lean_nat_add(v___x_2274_, v_size_2214_);
lean_dec(v___x_2274_);
v___x_2276_ = lean_nat_add(v___x_2213_, v_size_2214_);
v___x_2277_ = lean_nat_add(v___x_2276_, v_size_2232_);
lean_dec(v___x_2276_);
lean_inc_ref(v_r_2068_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v_r_2068_);
lean_ctor_set(v___x_2229_, 3, v_r_2219_);
lean_ctor_set(v___x_2229_, 2, v_v_2066_);
lean_ctor_set(v___x_2229_, 1, v_k_2065_);
lean_ctor_set(v___x_2229_, 0, v___x_2277_);
v___x_2279_ = v___x_2229_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_r_2219_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_r_2068_);
v___x_2279_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_isSharedCheck_2286_ = !lean_is_exclusive(v_r_2068_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; lean_object* v_unused_2291_; 
v_unused_2287_ = lean_ctor_get(v_r_2068_, 4);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_r_2068_, 3);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_r_2068_, 2);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_r_2068_, 1);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_r_2068_, 0);
lean_dec(v_unused_2291_);
v___x_2281_ = v_r_2068_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_r_2068_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v___x_2279_);
lean_ctor_set(v___x_2281_, 3, v_l_2218_);
lean_ctor_set(v___x_2281_, 2, v_v_2217_);
lean_ctor_set(v___x_2281_, 1, v_k_2216_);
lean_ctor_set(v___x_2281_, 0, v___x_2275_);
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_l_2218_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2299_; 
v_l_2299_ = lean_ctor_get(v_impl_2212_, 3);
lean_inc(v_l_2299_);
if (lean_obj_tag(v_l_2299_) == 0)
{
lean_object* v_r_2300_; lean_object* v_k_2301_; lean_object* v_v_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2313_; 
v_r_2300_ = lean_ctor_get(v_impl_2212_, 4);
v_k_2301_ = lean_ctor_get(v_impl_2212_, 1);
v_v_2302_ = lean_ctor_get(v_impl_2212_, 2);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2314_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2315_);
v___x_2304_ = v_impl_2212_;
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_r_2300_);
lean_inc(v_v_2302_);
lean_inc(v_k_2301_);
lean_dec(v_impl_2212_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2300_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 3, v_r_2300_);
lean_ctor_set(v___x_2304_, 2, v_v_2066_);
lean_ctor_set(v___x_2304_, 1, v_k_2065_);
lean_ctor_set(v___x_2304_, 0, v___x_2213_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_r_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_r_2300_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2308_);
lean_ctor_set(v___x_2070_, 3, v_l_2299_);
lean_ctor_set(v___x_2070_, 2, v_v_2302_);
lean_ctor_set(v___x_2070_, 1, v_k_2301_);
lean_ctor_set(v___x_2070_, 0, v___x_2306_);
v___x_2310_ = v___x_2070_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_2301_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v___x_2308_);
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
else
{
lean_object* v_r_2316_; 
v_r_2316_ = lean_ctor_get(v_impl_2212_, 4);
lean_inc(v_r_2316_);
if (lean_obj_tag(v_r_2316_) == 0)
{
lean_object* v_k_2317_; lean_object* v_v_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2341_; 
v_k_2317_ = lean_ctor_get(v_impl_2212_, 1);
v_v_2318_ = lean_ctor_get(v_impl_2212_, 2);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; 
v_unused_2342_ = lean_ctor_get(v_impl_2212_, 4);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2344_);
v___x_2320_ = v_impl_2212_;
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_v_2318_);
lean_inc(v_k_2317_);
lean_dec(v_impl_2212_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_k_2322_; lean_object* v_v_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_k_2322_ = lean_ctor_get(v_r_2316_, 1);
v_v_2323_ = lean_ctor_get(v_r_2316_, 2);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_r_2316_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; lean_object* v_unused_2340_; 
v_unused_2338_ = lean_ctor_get(v_r_2316_, 4);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2316_, 3);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2316_, 0);
lean_dec(v_unused_2340_);
v___x_2325_ = v_r_2316_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
lean_dec(v_r_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(3u);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v_l_2299_);
lean_ctor_set(v___x_2325_, 3, v_l_2299_);
lean_ctor_set(v___x_2325_, 2, v_v_2318_);
lean_ctor_set(v___x_2325_, 1, v_k_2317_);
lean_ctor_set(v___x_2325_, 0, v___x_2213_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2317_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2318_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_l_2299_);
v___x_2329_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 4, v_l_2299_);
lean_ctor_set(v___x_2320_, 2, v_v_2066_);
lean_ctor_set(v___x_2320_, 1, v_k_2065_);
lean_ctor_set(v___x_2320_, 0, v___x_2213_);
v___x_2331_ = v___x_2320_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2299_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2331_);
lean_ctor_set(v___x_2070_, 3, v___x_2329_);
lean_ctor_set(v___x_2070_, 2, v_v_2323_);
lean_ctor_set(v___x_2070_, 1, v_k_2322_);
lean_ctor_set(v___x_2070_, 0, v___x_2327_);
v___x_2333_ = v___x_2070_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_unsigned_to_nat(2u);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_r_2316_);
lean_ctor_set(v___x_2070_, 3, v_impl_2212_);
lean_ctor_set(v___x_2070_, 0, v___x_2345_);
v___x_2347_ = v___x_2070_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_impl_2212_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_2316_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_k_2061_);
lean_ctor_set(v___x_2351_, 2, v_v_2062_);
lean_ctor_set(v___x_2351_, 3, v_t_2063_);
lean_ctor_set(v___x_2351_, 4, v_t_2063_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2352_, lean_object* v_v_2353_, lean_object* v_x_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v_optionsPerPos_2364_; lean_object* v_currNamespace_2365_; lean_object* v_openDecls_2366_; uint8_t v_inPattern_2367_; lean_object* v_subExpr_2368_; lean_object* v_depth_2369_; lean_object* v_lctxInitIndices_2370_; lean_object* v___y_2372_; lean_object* v___x_2377_; 
v___x_2362_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2355_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2362_);
v_optionsPerPos_2364_ = lean_ctor_get(v_a_2355_, 0);
v_currNamespace_2365_ = lean_ctor_get(v_a_2355_, 1);
v_openDecls_2366_ = lean_ctor_get(v_a_2355_, 2);
v_inPattern_2367_ = lean_ctor_get_uint8(v_a_2355_, sizeof(void*)*6);
v_subExpr_2368_ = lean_ctor_get(v_a_2355_, 3);
v_depth_2369_ = lean_ctor_get(v_a_2355_, 4);
v_lctxInitIndices_2370_ = lean_ctor_get(v_a_2355_, 5);
v___x_2377_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2364_, v_a_2363_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Options_empty;
v___y_2372_ = v___x_2378_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2379_; 
v_val_2379_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_val_2379_);
lean_dec_ref_known(v___x_2377_, 1);
v___y_2372_ = v_val_2379_;
goto v___jp_2371_;
}
v___jp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2373_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2372_, v_k_2352_, v_v_2353_);
lean_inc(v_optionsPerPos_2364_);
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2363_, v___x_2373_, v_optionsPerPos_2364_);
lean_inc(v_lctxInitIndices_2370_);
lean_inc(v_depth_2369_);
lean_inc_ref(v_subExpr_2368_);
lean_inc(v_openDecls_2366_);
lean_inc(v_currNamespace_2365_);
v___x_2375_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v_currNamespace_2365_);
lean_ctor_set(v___x_2375_, 2, v_openDecls_2366_);
lean_ctor_set(v___x_2375_, 3, v_subExpr_2368_);
lean_ctor_set(v___x_2375_, 4, v_depth_2369_);
lean_ctor_set(v___x_2375_, 5, v_lctxInitIndices_2370_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*6, v_inPattern_2367_);
lean_inc(v_a_2360_);
lean_inc_ref(v_a_2359_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc(v_a_2356_);
v___x_2376_ = lean_apply_7(v_x_2354_, v___x_2375_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, lean_box(0));
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2380_, lean_object* v_v_2381_, lean_object* v_x_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2380_, v_v_2381_, v_x_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2391_, lean_object* v_k_2392_, lean_object* v_v_2393_, lean_object* v_x_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2392_, v_v_2393_, v_x_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2403_, lean_object* v_k_2404_, lean_object* v_v_2405_, lean_object* v_x_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2403_, v_k_2404_, v_v_2405_, v_x_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2415_, lean_object* v_k_2416_, lean_object* v_v_2417_, lean_object* v_t_2418_, lean_object* v_hl_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2416_, v_v_2417_, v_t_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2421_, lean_object* v_stx_2422_){
_start:
{
uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = 0;
lean_inc(v_pos_2421_);
v___x_2424_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2424_, 0, v_pos_2421_);
lean_ctor_set(v___x_2424_, 1, v_pos_2421_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_setInfo(v___x_2424_, v_stx_2422_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2438_; 
v___x_2429_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2427_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2430_, v_stx_2426_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2439_, v_a_2440_);
lean_dec_ref(v_a_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2443_, v_a_2444_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2463_, lean_object* v_e_2464_, uint8_t v_isBinder_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_lctx_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_lctx_2468_ = lean_ctor_get(v_a_2466_, 2);
v___x_2469_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v_stx_2463_);
v___x_2471_ = lean_box(0);
v___x_2472_ = 0;
lean_inc_ref(v_lctx_2468_);
v___x_2473_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2473_, 0, v___x_2470_);
lean_ctor_set(v___x_2473_, 1, v_lctx_2468_);
lean_ctor_set(v___x_2473_, 2, v___x_2471_);
lean_ctor_set(v___x_2473_, 3, v_e_2464_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*4, v_isBinder_2465_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*4 + 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2475_, lean_object* v_e_2476_, lean_object* v_isBinder_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
uint8_t v_isBinder_boxed_2480_; lean_object* v_res_2481_; 
v_isBinder_boxed_2480_ = lean_unbox(v_isBinder_2477_);
v_res_2481_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2475_, v_e_2476_, v_isBinder_boxed_2480_, v_a_2478_);
lean_dec_ref(v_a_2478_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2482_, lean_object* v_e_2483_, uint8_t v_isBinder_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2482_, v_e_2483_, v_isBinder_2484_, v_a_2487_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2493_, lean_object* v_e_2494_, lean_object* v_isBinder_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
uint8_t v_isBinder_boxed_2503_; lean_object* v_res_2504_; 
v_isBinder_boxed_2503_ = lean_unbox(v_isBinder_2495_);
v_res_2504_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2493_, v_e_2494_, v_isBinder_boxed_2503_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2505_, lean_object* v_stx_2506_, lean_object* v_e_2507_, uint8_t v_isBinder_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2535_; 
v___x_2512_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2506_, v_e_2507_, v_isBinder_2508_, v_a_2510_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_steps_2519_; lean_object* v_infos_2520_; lean_object* v_holeIter_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2534_; 
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2513_);
v___x_2518_ = lean_st_ref_take(v_a_2509_);
v_steps_2519_ = lean_ctor_get(v___x_2518_, 0);
v_infos_2520_ = lean_ctor_get(v___x_2518_, 1);
v_holeIter_2521_ = lean_ctor_get(v___x_2518_, 2);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2523_ = v___x_2518_;
v_isShared_2524_ = v_isSharedCheck_2534_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_holeIter_2521_);
lean_inc(v_infos_2520_);
lean_inc(v_steps_2519_);
lean_dec(v___x_2518_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2534_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2505_, v___x_2517_, v_infos_2520_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2526_);
v___x_2528_ = v___x_2523_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_steps_2519_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_holeIter_2521_);
v___x_2528_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_st_ref_put(v_a_2509_, v___x_2528_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2525_);
v___x_2531_ = v___x_2515_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2525_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2536_, lean_object* v_stx_2537_, lean_object* v_e_2538_, lean_object* v_isBinder_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
uint8_t v_isBinder_boxed_2543_; lean_object* v_res_2544_; 
v_isBinder_boxed_2543_ = lean_unbox(v_isBinder_2539_);
v_res_2544_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2536_, v_stx_2537_, v_e_2538_, v_isBinder_boxed_2543_, v_a_2540_, v_a_2541_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2545_, lean_object* v_stx_2546_, lean_object* v_e_2547_, uint8_t v_isBinder_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2545_, v_stx_2546_, v_e_2547_, v_isBinder_2548_, v_a_2550_, v_a_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2557_, lean_object* v_stx_2558_, lean_object* v_e_2559_, lean_object* v_isBinder_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
uint8_t v_isBinder_boxed_2568_; lean_object* v_res_2569_; 
v_isBinder_boxed_2568_ = lean_unbox(v_isBinder_2560_);
v_res_2569_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2557_, v_stx_2558_, v_e_2559_, v_isBinder_boxed_2568_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2570_, lean_object* v_fieldName_2571_, lean_object* v_stx_2572_, lean_object* v_val_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_lctx_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_lctx_2576_ = lean_ctor_get(v_a_2574_, 2);
lean_inc_ref(v_lctx_2576_);
v___x_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2577_, 0, v_projName_2570_);
lean_ctor_set(v___x_2577_, 1, v_fieldName_2571_);
lean_ctor_set(v___x_2577_, 2, v_lctx_2576_);
lean_ctor_set(v___x_2577_, 3, v_val_2573_);
lean_ctor_set(v___x_2577_, 4, v_stx_2572_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2579_, lean_object* v_fieldName_2580_, lean_object* v_stx_2581_, lean_object* v_val_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2579_, v_fieldName_2580_, v_stx_2581_, v_val_2582_, v_a_2583_);
lean_dec_ref(v_a_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2586_, lean_object* v_fieldName_2587_, lean_object* v_stx_2588_, lean_object* v_val_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2586_, v_fieldName_2587_, v_stx_2588_, v_val_2589_, v_a_2592_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2598_, lean_object* v_fieldName_2599_, lean_object* v_stx_2600_, lean_object* v_val_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2598_, v_fieldName_2599_, v_stx_2600_, v_val_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2610_, lean_object* v_projName_2611_, lean_object* v_fieldName_2612_, lean_object* v_stx_2613_, lean_object* v_val_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2641_; 
v___x_2618_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2611_, v_fieldName_2612_, v_stx_2613_, v_val_2614_, v_a_2616_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2641_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2641_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_steps_2625_; lean_object* v_infos_2626_; lean_object* v_holeIter_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2640_; 
v___x_2623_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_a_2619_);
v___x_2624_ = lean_st_ref_take(v_a_2615_);
v_steps_2625_ = lean_ctor_get(v___x_2624_, 0);
v_infos_2626_ = lean_ctor_get(v___x_2624_, 1);
v_holeIter_2627_ = lean_ctor_get(v___x_2624_, 2);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2629_ = v___x_2624_;
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_holeIter_2627_);
lean_inc(v_infos_2626_);
lean_inc(v_steps_2625_);
lean_dec(v___x_2624_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2631_ = lean_box(0);
v___x_2632_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2610_, v___x_2623_, v_infos_2626_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_steps_2625_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_holeIter_2627_);
v___x_2634_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2635_ = lean_st_ref_put(v_a_2615_, v___x_2634_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2631_);
v___x_2637_ = v___x_2621_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2631_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2642_, lean_object* v_projName_2643_, lean_object* v_fieldName_2644_, lean_object* v_stx_2645_, lean_object* v_val_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2642_, v_projName_2643_, v_fieldName_2644_, v_stx_2645_, v_val_2646_, v_a_2647_, v_a_2648_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2651_, lean_object* v_projName_2652_, lean_object* v_fieldName_2653_, lean_object* v_stx_2654_, lean_object* v_val_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2651_, v_projName_2652_, v_fieldName_2653_, v_stx_2654_, v_val_2655_, v_a_2657_, v_a_2658_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2664_, lean_object* v_projName_2665_, lean_object* v_fieldName_2666_, lean_object* v_stx_2667_, lean_object* v_val_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2664_, v_projName_2665_, v_fieldName_2666_, v_stx_2667_, v_val_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_val_2677_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2681_, v___y_2682_);
lean_dec_ref(v___y_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2685_, lean_object* v_stx_2686_, lean_object* v_e_2687_, uint8_t v_isBinder_2688_, lean_object* v_location_x3f_2689_, lean_object* v_docString_x3f_2690_, lean_object* v_mkDocString_x3f_2691_, uint8_t v_explicit_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v___x_2696_; lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2731_; 
v___x_2696_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2686_, v_e_2687_, v_isBinder_2688_, v_a_2694_);
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2731_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2731_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___y_2702_; 
if (lean_obj_tag(v_mkDocString_x3f_2691_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2690_) == 0)
{
v___y_2702_ = v_mkDocString_x3f_2691_;
goto v___jp_2701_;
}
else
{
lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2730_; 
v_val_2722_ = lean_ctor_get(v_docString_x3f_2690_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_docString_x3f_2690_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2724_ = v_docString_x3f_2690_;
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_dec(v_docString_x3f_2690_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___f_2726_; lean_object* v___x_2728_; 
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2726_, 0, v_val_2722_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___f_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___f_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
v___y_2702_ = v___x_2728_;
goto v___jp_2701_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2690_);
v___y_2702_ = v_mkDocString_x3f_2691_;
goto v___jp_2701_;
}
v___jp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v_steps_2706_; lean_object* v_infos_2707_; lean_object* v_holeIter_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2721_; 
v___x_2703_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2703_, 0, v_a_2697_);
lean_ctor_set(v___x_2703_, 1, v_location_x3f_2689_);
lean_ctor_set(v___x_2703_, 2, v___y_2702_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*3, v_explicit_2692_);
v___x_2704_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
v___x_2705_ = lean_st_ref_take(v_a_2693_);
v_steps_2706_ = lean_ctor_get(v___x_2705_, 0);
v_infos_2707_ = lean_ctor_get(v___x_2705_, 1);
v_holeIter_2708_ = lean_ctor_get(v___x_2705_, 2);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2710_ = v___x_2705_;
v_isShared_2711_ = v_isSharedCheck_2721_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_holeIter_2708_);
lean_inc(v_infos_2707_);
lean_inc(v_steps_2706_);
lean_dec(v___x_2705_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2721_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2685_, v___x_2704_, v_infos_2707_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v___x_2713_);
v___x_2715_ = v___x_2710_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_steps_2706_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_holeIter_2708_);
v___x_2715_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_st_ref_put(v_a_2693_, v___x_2715_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2712_);
v___x_2718_ = v___x_2699_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2712_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2732_, lean_object* v_stx_2733_, lean_object* v_e_2734_, lean_object* v_isBinder_2735_, lean_object* v_location_x3f_2736_, lean_object* v_docString_x3f_2737_, lean_object* v_mkDocString_x3f_2738_, lean_object* v_explicit_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
uint8_t v_isBinder_boxed_2743_; uint8_t v_explicit_boxed_2744_; lean_object* v_res_2745_; 
v_isBinder_boxed_2743_ = lean_unbox(v_isBinder_2735_);
v_explicit_boxed_2744_ = lean_unbox(v_explicit_2739_);
v_res_2745_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2732_, v_stx_2733_, v_e_2734_, v_isBinder_boxed_2743_, v_location_x3f_2736_, v_docString_x3f_2737_, v_mkDocString_x3f_2738_, v_explicit_boxed_2744_, v_a_2740_, v_a_2741_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2746_, lean_object* v_stx_2747_, lean_object* v_e_2748_, uint8_t v_isBinder_2749_, lean_object* v_location_x3f_2750_, lean_object* v_docString_x3f_2751_, lean_object* v_mkDocString_x3f_2752_, uint8_t v_explicit_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2746_, v_stx_2747_, v_e_2748_, v_isBinder_2749_, v_location_x3f_2750_, v_docString_x3f_2751_, v_mkDocString_x3f_2752_, v_explicit_2753_, v_a_2755_, v_a_2756_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2762_, lean_object* v_stx_2763_, lean_object* v_e_2764_, lean_object* v_isBinder_2765_, lean_object* v_location_x3f_2766_, lean_object* v_docString_x3f_2767_, lean_object* v_mkDocString_x3f_2768_, lean_object* v_explicit_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
uint8_t v_isBinder_boxed_2777_; uint8_t v_explicit_boxed_2778_; lean_object* v_res_2779_; 
v_isBinder_boxed_2777_ = lean_unbox(v_isBinder_2765_);
v_explicit_boxed_2778_ = lean_unbox(v_explicit_2769_);
v_res_2779_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2762_, v_stx_2763_, v_e_2764_, v_isBinder_boxed_2777_, v_location_x3f_2766_, v_docString_x3f_2767_, v_mkDocString_x3f_2768_, v_explicit_boxed_2778_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v_a_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_n(v_a_2786_, 2);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2781_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2781_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = 0;
v___x_2792_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2788_, v_a_2786_, v_a_2790_, v___x_2791_, v_a_2782_, v_a_2783_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2792_, 0);
lean_dec(v_unused_2800_);
v___x_2794_ = v___x_2792_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2792_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_a_2786_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2786_);
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
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2786_);
v_a_2801_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2792_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2833_, lean_object* v_t_2834_){
_start:
{
if (lean_obj_tag(v_t_2834_) == 0)
{
lean_object* v_k_2835_; lean_object* v_l_2836_; lean_object* v_r_2837_; uint8_t v___x_2838_; 
v_k_2835_ = lean_ctor_get(v_t_2834_, 1);
v_l_2836_ = lean_ctor_get(v_t_2834_, 3);
v_r_2837_ = lean_ctor_get(v_t_2834_, 4);
v___x_2838_ = lean_nat_dec_lt(v_k_2833_, v_k_2835_);
if (v___x_2838_ == 0)
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_nat_dec_eq(v_k_2833_, v_k_2835_);
if (v___x_2839_ == 0)
{
v_t_2834_ = v_r_2837_;
goto _start;
}
else
{
return v___x_2839_;
}
}
else
{
v_t_2834_ = v_l_2836_;
goto _start;
}
}
else
{
uint8_t v___x_2842_; 
v___x_2842_ = 0;
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2843_, lean_object* v_t_2844_){
_start:
{
uint8_t v_res_2845_; lean_object* v_r_2846_; 
v_res_2845_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2843_, v_t_2844_);
lean_dec(v_t_2844_);
lean_dec(v_k_2843_);
v_r_2846_ = lean_box(v_res_2845_);
return v_r_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Syntax_getInfo_x3f(v_stx_2847_);
if (lean_obj_tag(v___x_2852_) == 1)
{
lean_object* v_val_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2871_; 
v_val_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_val_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_val_2853_) == 1)
{
uint8_t v_canonical_2857_; 
v_canonical_2857_ = lean_ctor_get_uint8(v_val_2853_, sizeof(void*)*2);
if (v_canonical_2857_ == 0)
{
lean_object* v_pos_2858_; lean_object* v_endPos_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_pos_2858_ = lean_ctor_get(v_val_2853_, 0);
lean_inc(v_pos_2858_);
v_endPos_2859_ = lean_ctor_get(v_val_2853_, 1);
lean_inc(v_endPos_2859_);
lean_dec_ref_known(v_val_2853_, 2);
v___x_2860_ = lean_st_ref_get(v_a_2849_);
v___x_2861_ = lean_nat_dec_eq(v_pos_2858_, v_endPos_2859_);
lean_dec(v_endPos_2859_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec(v___x_2860_);
lean_dec(v_pos_2858_);
lean_del_object(v___x_2855_);
v___x_2862_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2862_;
}
else
{
lean_object* v_infos_2863_; uint8_t v___x_2864_; 
v_infos_2863_ = lean_ctor_get(v___x_2860_, 1);
lean_inc(v_infos_2863_);
lean_dec(v___x_2860_);
v___x_2864_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2858_, v_infos_2863_);
lean_dec(v_infos_2863_);
lean_dec(v_pos_2858_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_del_object(v___x_2855_);
v___x_2865_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2865_;
}
else
{
lean_object* v___x_2867_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 0);
lean_ctor_set(v___x_2855_, 0, v_stx_2847_);
v___x_2867_ = v___x_2855_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_stx_2847_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v___x_2869_; 
lean_dec_ref_known(v_val_2853_, 2);
lean_del_object(v___x_2855_);
v___x_2869_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2869_;
}
}
else
{
lean_object* v___x_2870_; 
lean_del_object(v___x_2855_);
lean_dec(v_val_2853_);
v___x_2870_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2870_;
}
}
}
else
{
lean_object* v___x_2872_; 
lean_dec(v___x_2852_);
v___x_2872_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
return v_res_2896_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2897_, lean_object* v_k_2898_, lean_object* v_t_2899_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2898_, v_t_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2901_, lean_object* v_k_2902_, lean_object* v_t_2903_){
_start:
{
uint8_t v_res_2904_; lean_object* v_r_2905_; 
v_res_2904_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2901_, v_k_2902_, v_t_2903_);
lean_dec(v_t_2903_);
lean_dec(v_k_2902_);
v_r_2905_ = lean_box(v_res_2904_);
return v_r_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; 
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
lean_inc(v_a_2910_);
lean_inc_ref(v_a_2909_);
lean_inc(v_a_2908_);
lean_inc_ref(v_a_2907_);
v___x_2914_ = lean_apply_7(v_d_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, lean_box(0));
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2915_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2916_;
}
else
{
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2934_; 
lean_inc(v_a_2932_);
lean_inc_ref(v_a_2931_);
lean_inc(v_a_2930_);
lean_inc_ref(v_a_2929_);
lean_inc(v_a_2928_);
lean_inc_ref(v_a_2927_);
v___x_2934_ = lean_apply_7(v_d_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, lean_box(0));
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2935_, v_a_2927_, v_a_2928_, v_a_2929_);
return v___x_2936_;
}
else
{
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2945_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2946_, lean_object* v_suggestion_x27_2947_, lean_object* v_x_2948_){
_start:
{
if (lean_obj_tag(v_x_2948_) == 1)
{
lean_object* v_fvarId_2949_; lean_object* v___x_2950_; 
v_fvarId_2949_ = lean_ctor_get(v_x_2948_, 0);
lean_inc(v_fvarId_2949_);
lean_dec_ref_known(v_x_2948_, 1);
v___x_2950_ = lean_local_ctx_find(v_lctx_2946_, v_fvarId_2949_);
if (lean_obj_tag(v___x_2950_) == 0)
{
uint8_t v___x_2951_; 
v___x_2951_ = 0;
return v___x_2951_;
}
else
{
lean_object* v_val_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_val_2952_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_val_2952_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2953_ = l_Lean_LocalDecl_userName(v_val_2952_);
lean_dec(v_val_2952_);
v___x_2954_ = lean_name_eq(v___x_2953_, v_suggestion_x27_2947_);
lean_dec(v___x_2953_);
return v___x_2954_;
}
}
else
{
uint8_t v___x_2955_; 
lean_dec_ref(v_x_2948_);
lean_dec_ref(v_lctx_2946_);
v___x_2955_ = 0;
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2956_, lean_object* v_suggestion_x27_2957_, lean_object* v_x_2958_){
_start:
{
uint8_t v_res_2959_; lean_object* v_r_2960_; 
v_res_2959_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2956_, v_suggestion_x27_2957_, v_x_2958_);
lean_dec(v_suggestion_x27_2957_);
v_r_2960_ = lean_box(v_res_2959_);
return v_r_2960_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2961_, lean_object* v_lctx_2962_, lean_object* v_suggestion_x27_2963_){
_start:
{
lean_object* v___f_2964_; lean_object* v___x_2965_; 
v___f_2964_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2964_, 0, v_lctx_2962_);
lean_closure_set(v___f_2964_, 1, v_suggestion_x27_2963_);
v___x_2965_ = lean_find_expr(v___f_2964_, v_body_2961_);
lean_dec_ref(v___f_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
uint8_t v___x_2966_; 
v___x_2966_ = 0;
return v___x_2966_;
}
else
{
uint8_t v___x_2967_; 
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = 1;
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2968_, lean_object* v_lctx_2969_, lean_object* v_suggestion_x27_2970_){
_start:
{
uint8_t v_res_2971_; lean_object* v_r_2972_; 
v_res_2971_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2968_, v_lctx_2969_, v_suggestion_x27_2970_);
lean_dec_ref(v_body_2968_);
v_r_2972_ = lean_box(v_res_2971_);
return v_r_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_toCold_2977_; lean_object* v_quotContext_2978_; lean_object* v_currMacroScope_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_toCold_2977_ = lean_ctor_get(v___y_2974_, 0);
lean_inc_ref(v_toCold_2977_);
lean_dec_ref(v___y_2974_);
v_quotContext_2978_ = lean_ctor_get(v_toCold_2977_, 8);
lean_inc(v_quotContext_2978_);
v_currMacroScope_2979_ = lean_ctor_get(v_toCold_2977_, 9);
lean_inc(v_currMacroScope_2979_);
lean_dec_ref(v_toCold_2977_);
v___x_2980_ = l_Lean_addMacroScope(v_quotContext_2978_, v_snd_2973_, v_currMacroScope_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_2991_, lean_object* v_body_2992_, uint8_t v_preserveName_2993_, lean_object* v_avoid_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; uint8_t v_fst_3034_; lean_object* v_snd_3035_; uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Name_isAnonymous(v_suggestion_2991_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = l_Lean_Name_hasMacroScopes(v_suggestion_2991_);
v___x_3043_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2991_);
v_fst_3034_ = v___x_3042_;
v_snd_3035_ = v___x_3043_;
goto v___jp_3033_;
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3034_ = v___x_3041_;
v_snd_3035_ = v___x_3044_;
goto v___jp_3033_;
}
v___jp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = l_Lean_LocalContext_getUnusedName(v___y_3004_, v___y_3003_);
lean_dec(v___y_3003_);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
v___jp_3007_:
{
if (v_preserveName_2993_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___y_3008_);
v___x_3011_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3012_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3011_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3023_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_unbox(v_a_3013_);
lean_dec(v_a_3013_);
if (v___x_3017_ == 0)
{
lean_del_object(v___x_3015_);
v___y_3003_ = v___y_3009_;
v___y_3004_ = v___y_3010_;
goto v___jp_3002_;
}
else
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_NameSet_contains(v_avoid_2994_, v___y_3009_);
if (v___x_3018_ == 0)
{
uint8_t v___x_3019_; 
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3010_);
v___x_3019_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2992_, v___y_3010_, v___y_3009_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3021_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___y_3009_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___y_3009_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
else
{
lean_del_object(v___x_3015_);
v___y_3003_ = v___y_3009_;
v___y_3004_ = v___y_3010_;
goto v___jp_3002_;
}
}
else
{
lean_del_object(v___x_3015_);
v___y_3003_ = v___y_3009_;
v___y_3004_ = v___y_3010_;
goto v___jp_3002_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v___y_3009_);
v_a_3024_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3012_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3012_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec(v___y_3009_);
v___x_3032_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3008_, v_a_2999_, v_a_3000_);
return v___x_3032_;
}
}
v___jp_3033_:
{
lean_object* v_lctx_3036_; uint8_t v___x_3037_; 
v_lctx_3036_ = lean_ctor_get(v_a_2997_, 2);
v___x_3037_ = l_Lean_LocalContext_usesUserName(v_lctx_3036_, v_snd_3035_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_snd_3035_);
return v___x_3038_;
}
else
{
lean_object* v___f_3039_; 
lean_inc(v_snd_3035_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3039_, 0, v_snd_3035_);
if (v_preserveName_2993_ == 0)
{
v___y_3008_ = v___f_3039_;
v___y_3009_ = v_snd_3035_;
v___y_3010_ = v_lctx_3036_;
goto v___jp_3007_;
}
else
{
if (v_fst_3034_ == 0)
{
lean_object* v___x_3040_; 
lean_dec_ref(v___f_3039_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_snd_3035_);
return v___x_3040_;
}
else
{
v___y_3008_ = v___f_3039_;
v___y_3009_ = v_snd_3035_;
v___y_3010_ = v_lctx_3036_;
goto v___jp_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3045_, lean_object* v_body_3046_, lean_object* v_preserveName_3047_, lean_object* v_avoid_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
uint8_t v_preserveName_boxed_3056_; lean_object* v_res_3057_; 
v_preserveName_boxed_3056_ = lean_unbox(v_preserveName_3047_);
v_res_3057_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3045_, v_body_3046_, v_preserveName_boxed_3056_, v_avoid_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_avoid_3048_);
lean_dec_ref(v_body_3046_);
lean_dec(v_suggestion_3045_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v_holeIter_3061_; lean_object* v_curr_3062_; lean_object* v___x_3063_; lean_object* v_steps_3064_; lean_object* v_infos_3065_; lean_object* v_holeIter_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3076_; 
v___x_3060_ = lean_st_ref_get(v___y_3058_);
v_holeIter_3061_ = lean_ctor_get(v___x_3060_, 2);
lean_inc_ref(v_holeIter_3061_);
lean_dec(v___x_3060_);
v_curr_3062_ = lean_ctor_get(v_holeIter_3061_, 0);
lean_inc(v_curr_3062_);
lean_dec_ref(v_holeIter_3061_);
v___x_3063_ = lean_st_ref_take(v___y_3058_);
v_steps_3064_ = lean_ctor_get(v___x_3063_, 0);
v_infos_3065_ = lean_ctor_get(v___x_3063_, 1);
v_holeIter_3066_ = lean_ctor_get(v___x_3063_, 2);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3068_ = v___x_3063_;
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_holeIter_3066_);
lean_inc(v_infos_3065_);
lean_inc(v_steps_3064_);
lean_dec(v___x_3063_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3070_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3066_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 2, v___x_3070_);
v___x_3072_ = v___x_3068_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_steps_3064_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_infos_3065_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_st_ref_put(v___y_3058_, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_curr_3062_);
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3077_);
lean_dec(v___y_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3081_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3096_, lean_object* v_e_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v_a_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3105_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3099_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_n(v_a_3106_, 2);
lean_dec_ref(v___x_3105_);
v___x_3107_ = l_Lean_mkIdent(v_n_3096_);
v___x_3108_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3106_, v___x_3107_);
v___x_3109_ = 0;
lean_inc(v___x_3108_);
v___x_3110_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3106_, v___x_3108_, v_e_3097_, v___x_3109_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3110_, 0);
lean_dec(v_unused_3118_);
v___x_3112_ = v___x_3110_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v___x_3110_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3108_);
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3108_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v___x_3108_);
v_a_3119_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3110_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3127_, lean_object* v_e_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3127_, v_e_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; 
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
v___x_3146_ = lean_apply_8(v_d_3137_, v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, lean_box(0));
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3147_, lean_object* v_x_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3147_, v_x_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; 
lean_inc(v___y_3164_);
lean_inc_ref(v___y_3163_);
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
v___x_3166_ = lean_apply_8(v_k_3157_, v_b_3160_, v___y_3158_, v___y_3159_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, lean_box(0));
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3167_, v___y_3168_, v___y_3169_, v_b_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3177_, uint8_t v_bi_3178_, lean_object* v_type_3179_, lean_object* v_k_3180_, uint8_t v_kind_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___f_3189_; lean_object* v___x_3190_; 
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v___f_3189_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3189_, 0, v_k_3180_);
lean_closure_set(v___f_3189_, 1, v___y_3182_);
lean_closure_set(v___f_3189_, 2, v___y_3183_);
v___x_3190_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3177_, v_bi_3178_, v_type_3179_, v___f_3189_, v_kind_3181_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3190_) == 0)
{
return v___x_3190_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3199_, lean_object* v_bi_3200_, lean_object* v_type_3201_, lean_object* v_k_3202_, lean_object* v_kind_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v_bi_boxed_3211_; uint8_t v_kind_boxed_3212_; lean_object* v_res_3213_; 
v_bi_boxed_3211_ = lean_unbox(v_bi_3200_);
v_kind_boxed_3212_ = lean_unbox(v_kind_3203_);
v_res_3213_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3199_, v_bi_boxed_3211_, v_type_3201_, v_k_3202_, v_kind_boxed_3212_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3214_, lean_object* v_childIdx_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_subExpr_3224_; lean_object* v_optionsPerPos_3225_; lean_object* v_currNamespace_3226_; lean_object* v_openDecls_3227_; uint8_t v_inPattern_3228_; lean_object* v_depth_3229_; lean_object* v_lctxInitIndices_3230_; lean_object* v_pos_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_subExpr_3224_ = lean_ctor_get(v___y_3217_, 3);
v_optionsPerPos_3225_ = lean_ctor_get(v___y_3217_, 0);
v_currNamespace_3226_ = lean_ctor_get(v___y_3217_, 1);
v_openDecls_3227_ = lean_ctor_get(v___y_3217_, 2);
v_inPattern_3228_ = lean_ctor_get_uint8(v___y_3217_, sizeof(void*)*6);
v_depth_3229_ = lean_ctor_get(v___y_3217_, 4);
v_lctxInitIndices_3230_ = lean_ctor_get(v___y_3217_, 5);
v_pos_3231_ = lean_ctor_get(v_subExpr_3224_, 1);
v___x_3232_ = l_Lean_SubExpr_Pos_push(v_pos_3231_, v_childIdx_3215_);
v___x_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_child_3214_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
lean_inc(v_lctxInitIndices_3230_);
lean_inc(v_depth_3229_);
lean_inc(v_openDecls_3227_);
lean_inc(v_currNamespace_3226_);
lean_inc(v_optionsPerPos_3225_);
v___x_3234_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3234_, 0, v_optionsPerPos_3225_);
lean_ctor_set(v___x_3234_, 1, v_currNamespace_3226_);
lean_ctor_set(v___x_3234_, 2, v_openDecls_3227_);
lean_ctor_set(v___x_3234_, 3, v___x_3233_);
lean_ctor_set(v___x_3234_, 4, v_depth_3229_);
lean_ctor_set(v___x_3234_, 5, v_lctxInitIndices_3230_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*6, v_inPattern_3228_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
v___x_3235_ = lean_apply_7(v_x_3216_, v___x_3234_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3236_, lean_object* v_childIdx_3237_, lean_object* v_x_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3236_, v_childIdx_3237_, v_x_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3247_, lean_object* v_a_3248_, lean_object* v_x_3249_, lean_object* v_fvar_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; 
lean_inc(v___y_3256_);
lean_inc_ref(v___y_3255_);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3253_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3251_);
lean_inc_ref(v_fvar_3250_);
v___x_3258_ = lean_apply_8(v_v_3247_, v_fvar_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, lean_box(0));
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = l_Lean_Expr_bindingBody_x21(v_a_3248_);
v___x_3261_ = lean_expr_instantiate1(v___x_3260_, v_fvar_3250_);
lean_dec_ref(v_fvar_3250_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = lean_apply_1(v_x_3249_, v_a_3259_);
v___x_3264_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3261_, v___x_3262_, v___x_3263_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
return v___x_3264_;
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_fvar_3250_);
lean_dec_ref(v_x_3249_);
v_a_3265_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3258_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3258_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_, lean_object* v_fvar_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3273_, v_a_3274_, v_x_3275_, v_fvar_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_a_3274_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3285_, lean_object* v_v_3286_, lean_object* v_x_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v_a_3296_; lean_object* v___f_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
v___x_3295_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3288_);
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_n(v_a_3296_, 2);
lean_dec_ref(v___x_3295_);
v___f_3297_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3297_, 0, v_v_3286_);
lean_closure_set(v___f_3297_, 1, v_a_3296_);
lean_closure_set(v___f_3297_, 2, v_x_3287_);
v___x_3298_ = l_Lean_Expr_binderInfo(v_a_3296_);
v___x_3299_ = l_Lean_Expr_bindingDomain_x21(v_a_3296_);
lean_dec(v_a_3296_);
v___x_3300_ = 0;
v___x_3301_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3285_, v___x_3298_, v___x_3299_, v___f_3297_, v___x_3300_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3302_, lean_object* v_v_3303_, lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3302_, v_v_3303_, v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3313_, uint8_t v_preserveName_3314_, lean_object* v_avoid_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___f_3323_; lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___f_3323_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3323_, 0, v_d_3313_);
v___x_3324_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3316_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3316_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = l_Lean_Expr_bindingName_x21(v_a_3325_);
lean_dec(v_a_3325_);
v___x_3329_ = l_Lean_Expr_bindingBody_x21(v_a_3327_);
lean_dec(v_a_3327_);
v___x_3330_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3328_, v___x_3329_, v_preserveName_3314_, v_avoid_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
lean_dec_ref(v___x_3329_);
lean_dec(v___x_3328_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc_n(v_a_3331_, 2);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3332_, 0, v_a_3331_);
v___x_3333_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3331_, v___x_3332_, v___f_3323_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_3333_;
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref(v___f_3323_);
v_a_3334_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3330_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3330_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3342_, lean_object* v_preserveName_3343_, lean_object* v_avoid_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
uint8_t v_preserveName_boxed_3352_; lean_object* v_res_3353_; 
v_preserveName_boxed_3352_ = lean_unbox(v_preserveName_3343_);
v_res_3353_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3342_, v_preserveName_boxed_3352_, v_avoid_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_avoid_3344_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3354_, lean_object* v_d_3355_, uint8_t v_preserveName_3356_, lean_object* v_avoid_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3355_, v_preserveName_3356_, v_avoid_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_d_3367_, lean_object* v_preserveName_3368_, lean_object* v_avoid_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
uint8_t v_preserveName_boxed_3377_; lean_object* v_res_3378_; 
v_preserveName_boxed_3377_ = lean_unbox(v_preserveName_3368_);
v_res_3378_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3366_, v_d_3367_, v_preserveName_boxed_3377_, v_avoid_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_avoid_3369_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3379_, lean_object* v_child_3380_, lean_object* v_childIdx_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3380_, v_childIdx_3381_, v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3391_, lean_object* v_child_3392_, lean_object* v_childIdx_3393_, lean_object* v_x_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3391_, v_child_3392_, v_childIdx_3393_, v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3403_, lean_object* v_name_3404_, uint8_t v_bi_3405_, lean_object* v_type_3406_, lean_object* v_k_3407_, uint8_t v_kind_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3404_, v_bi_3405_, v_type_3406_, v_k_3407_, v_kind_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3417_, lean_object* v_name_3418_, lean_object* v_bi_3419_, lean_object* v_type_3420_, lean_object* v_k_3421_, lean_object* v_kind_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
uint8_t v_bi_boxed_3430_; uint8_t v_kind_boxed_3431_; lean_object* v_res_3432_; 
v_bi_boxed_3430_ = lean_unbox(v_bi_3419_);
v_kind_boxed_3431_ = lean_unbox(v_kind_3422_);
v_res_3432_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3417_, v_name_3418_, v_bi_boxed_3430_, v_type_3420_, v_k_3421_, v_kind_boxed_3431_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3433_, lean_object* v_00_u03b2_3434_, lean_object* v_n_3435_, lean_object* v_v_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3435_, v_v_3436_, v_x_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3446_, lean_object* v_00_u03b2_3447_, lean_object* v_n_3448_, lean_object* v_v_3449_, lean_object* v_x_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3446_, v_00_u03b2_3447_, v_n_3448_, v_v_3449_, v_x_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object* v_x_3459_){
_start:
{
switch(lean_obj_tag(v_x_3459_))
{
case 0:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
return v___x_3460_;
}
case 1:
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_unsigned_to_nat(1u);
return v___x_3461_;
}
case 2:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_unsigned_to_nat(2u);
return v___x_3462_;
}
default: 
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_unsigned_to_nat(3u);
return v___x_3463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object* v_x_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(v_x_3464_);
lean_dec(v_x_3464_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3466_, lean_object* v_k_3467_){
_start:
{
if (lean_obj_tag(v_t_3466_) == 3)
{
lean_object* v_s_3468_; lean_object* v___x_3469_; 
v_s_3468_ = lean_ctor_get(v_t_3466_, 0);
lean_inc_ref(v_s_3468_);
lean_dec_ref_known(v_t_3466_, 1);
v___x_3469_ = lean_apply_1(v_k_3467_, v_s_3468_);
return v___x_3469_;
}
else
{
lean_dec(v_t_3466_);
return v_k_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3470_, lean_object* v_ctorIdx_3471_, lean_object* v_t_3472_, lean_object* v_h_3473_, lean_object* v_k_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3472_, v_k_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3476_, lean_object* v_ctorIdx_3477_, lean_object* v_t_3478_, lean_object* v_h_3479_, lean_object* v_k_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3476_, v_ctorIdx_3477_, v_t_3478_, v_h_3479_, v_k_3480_);
lean_dec(v_ctorIdx_3477_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3482_, lean_object* v_deep_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3482_, v_deep_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3485_, lean_object* v_t_3486_, lean_object* v_h_3487_, lean_object* v_deep_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3486_, v_deep_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3490_, lean_object* v_proof_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3490_, v_proof_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3493_, lean_object* v_t_3494_, lean_object* v_h_3495_, lean_object* v_proof_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3494_, v_proof_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3498_, lean_object* v_maxSteps_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3498_, v_maxSteps_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3501_, lean_object* v_t_3502_, lean_object* v_h_3503_, lean_object* v_maxSteps_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3502_, v_maxSteps_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3506_, lean_object* v_string_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3506_, v_string_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3509_, lean_object* v_t_3510_, lean_object* v_h_3511_, lean_object* v_string_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3510_, v_string_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3517_){
_start:
{
switch(lean_obj_tag(v_x_3517_))
{
case 0:
{
lean_object* v___x_3518_; 
v___x_3518_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3518_;
}
case 1:
{
lean_object* v___x_3519_; 
v___x_3519_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3519_;
}
case 2:
{
lean_object* v___x_3520_; 
v___x_3520_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3520_;
}
default: 
{
lean_object* v_s_3521_; 
v_s_3521_ = lean_ctor_get(v_x_3517_, 0);
lean_inc_ref(v_s_3521_);
return v_s_3521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3522_);
lean_dec(v_x_3522_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3524_, lean_object* v_stx_3525_, lean_object* v_e_3526_, lean_object* v_reason_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
uint8_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3531_ = 0;
v___x_3532_ = lean_box(0);
v___x_3533_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3527_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
v___x_3535_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3524_, v_stx_3525_, v_e_3526_, v___x_3531_, v___x_3532_, v___x_3534_, v___x_3532_, v___x_3531_, v_a_3528_, v_a_3529_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3536_, lean_object* v_stx_3537_, lean_object* v_e_3538_, lean_object* v_reason_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3536_, v_stx_3537_, v_e_3538_, v_reason_3539_, v_a_3540_, v_a_3541_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec(v_reason_3539_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3544_, lean_object* v_stx_3545_, lean_object* v_e_3546_, lean_object* v_reason_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3544_, v_stx_3545_, v_e_3546_, v_reason_3547_, v_a_3549_, v_a_3550_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3556_, lean_object* v_stx_3557_, lean_object* v_e_3558_, lean_object* v_reason_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3556_, v_stx_3557_, v_e_3558_, v_reason_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_reason_3559_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3568_, lean_object* v_ctx_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_optionsPerPos_3576_; lean_object* v_currNamespace_3577_; lean_object* v_openDecls_3578_; uint8_t v_inPattern_3579_; lean_object* v_subExpr_3580_; lean_object* v_depth_3581_; lean_object* v_lctxInitIndices_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_optionsPerPos_3576_ = lean_ctor_get(v_ctx_3569_, 0);
v_currNamespace_3577_ = lean_ctor_get(v_ctx_3569_, 1);
v_openDecls_3578_ = lean_ctor_get(v_ctx_3569_, 2);
v_inPattern_3579_ = lean_ctor_get_uint8(v_ctx_3569_, sizeof(void*)*6);
v_subExpr_3580_ = lean_ctor_get(v_ctx_3569_, 3);
v_depth_3581_ = lean_ctor_get(v_ctx_3569_, 4);
v_lctxInitIndices_3582_ = lean_ctor_get(v_ctx_3569_, 5);
v___x_3583_ = lean_unsigned_to_nat(1u);
v___x_3584_ = lean_nat_add(v_depth_3581_, v___x_3583_);
lean_inc(v_lctxInitIndices_3582_);
lean_inc_ref(v_subExpr_3580_);
lean_inc(v_openDecls_3578_);
lean_inc(v_currNamespace_3577_);
lean_inc(v_optionsPerPos_3576_);
v___x_3585_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3585_, 0, v_optionsPerPos_3576_);
lean_ctor_set(v___x_3585_, 1, v_currNamespace_3577_);
lean_ctor_set(v___x_3585_, 2, v_openDecls_3578_);
lean_ctor_set(v___x_3585_, 3, v_subExpr_3580_);
lean_ctor_set(v___x_3585_, 4, v___x_3584_);
lean_ctor_set(v___x_3585_, 5, v_lctxInitIndices_3582_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*6, v_inPattern_3579_);
lean_inc(v_a_3574_);
lean_inc_ref(v_a_3573_);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
lean_inc(v_a_3570_);
v___x_3586_ = lean_apply_7(v_act_3568_, v___x_3585_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, lean_box(0));
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3587_, lean_object* v_ctx_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3587_, v_ctx_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_ctx_3588_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3596_, lean_object* v_act_3597_, lean_object* v_ctx_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3597_, v_ctx_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3606_, lean_object* v_act_3607_, lean_object* v_ctx_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3606_, v_act_3607_, v_ctx_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_ctx_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3616_, lean_object* v_e_3617_){
_start:
{
lean_object* v___y_3619_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3623_ = lean_unsigned_to_nat(254u);
v___x_3624_ = lean_nat_dec_le(v___x_3623_, v_threshold_3616_);
if (v___x_3624_ == 0)
{
v___y_3619_ = v_threshold_3616_;
goto v___jp_3618_;
}
else
{
v___y_3619_ = v___x_3623_;
goto v___jp_3618_;
}
v___jp_3618_:
{
uint32_t v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3620_ = l_Lean_Expr_approxDepth(v_e_3617_);
v___x_3621_ = lean_uint32_to_nat(v___x_3620_);
v___x_3622_ = lean_nat_dec_le(v___x_3621_, v___y_3619_);
lean_dec(v___x_3621_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3625_, lean_object* v_e_3626_){
_start:
{
uint8_t v_res_3627_; lean_object* v_r_3628_; 
v_res_3627_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3625_, v_e_3626_);
lean_dec_ref(v_e_3626_);
lean_dec(v_threshold_3625_);
v_r_3628_ = lean_box(v_res_3627_);
return v_r_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
uint8_t v___x_3639_; 
v___x_3639_ = l_Lean_Expr_isAtomic(v_e_3631_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3641_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3640_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3684_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3684_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3684_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_unbox(v_a_3642_);
if (v___x_3646_ == 0)
{
lean_object* v_depth_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_del_object(v___x_3644_);
v_depth_3647_ = lean_ctor_get(v_a_3632_, 4);
v___x_3648_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3649_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3648_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3671_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3654_ = lean_nat_sub(v_depth_3647_, v_a_3650_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_nat_dec_lt(v___x_3655_, v___x_3654_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3658_; 
lean_dec(v___x_3654_);
lean_dec(v_a_3650_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_a_3642_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3642_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3660_ = lean_unsigned_to_nat(2u);
v___x_3661_ = lean_nat_shiftr(v_a_3650_, v___x_3660_);
lean_dec(v_a_3650_);
v___x_3662_ = lean_nat_sub(v___x_3661_, v___x_3654_);
lean_dec(v___x_3654_);
lean_dec(v___x_3661_);
v___x_3663_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3662_, v_e_3631_);
lean_dec(v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_dec(v_a_3642_);
v___x_3664_ = lean_box(v___x_3656_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3664_);
v___x_3666_ = v___x_3652_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
else
{
lean_object* v___x_3669_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_a_3642_);
v___x_3669_ = v___x_3652_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3642_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_a_3642_);
v_a_3672_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3649_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3649_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
lean_dec(v_a_3642_);
v___x_3680_ = lean_box(v___x_3639_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3680_);
v___x_3682_ = v___x_3644_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
return v___x_3641_;
}
}
else
{
uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = 0;
v___x_3686_ = lean_box(v___x_3685_);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec_ref(v_e_3688_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
uint8_t v___x_3707_; 
v___x_3707_ = l_Lean_Expr_isAtomic(v_e_3699_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3709_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3708_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3759_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3759_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3759_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___y_3715_; uint8_t v___x_3740_; 
v___x_3740_ = lean_unbox(v_a_3710_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_del_object(v___x_3712_);
lean_inc_ref(v_e_3699_);
v___x_3741_ = l_Lean_Meta_isProof(v_e_3699_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3741_) == 0)
{
v___y_3715_ = v___x_3741_;
goto v___jp_3714_;
}
else
{
lean_object* v_a_3742_; uint8_t v___y_3744_; uint8_t v___x_3753_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
v___x_3753_ = l_Lean_Exception_isInterrupt(v_a_3742_);
if (v___x_3753_ == 0)
{
uint8_t v___x_3754_; 
v___x_3754_ = l_Lean_Exception_isRuntime(v_a_3742_);
v___y_3744_ = v___x_3754_;
goto v___jp_3743_;
}
else
{
lean_dec(v_a_3742_);
v___y_3744_ = v___x_3753_;
goto v___jp_3743_;
}
v___jp_3743_:
{
if (v___y_3744_ == 0)
{
lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_e_3699_);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3752_);
v___x_3746_ = v___x_3741_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_dec(v___x_3741_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set_tag(v___x_3746_, 0);
lean_ctor_set(v___x_3746_, 0, v_a_3710_);
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3710_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
v___y_3715_ = v___x_3741_;
goto v___jp_3714_;
}
}
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_dec(v_a_3710_);
lean_dec_ref(v_e_3699_);
v___x_3755_ = lean_box(v___x_3707_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3755_);
v___x_3757_ = v___x_3712_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
v___jp_3714_:
{
if (lean_obj_tag(v___y_3715_) == 0)
{
lean_object* v_a_3716_; uint8_t v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___y_3715_, 0);
v___x_3717_ = lean_unbox(v_a_3716_);
if (v___x_3717_ == 0)
{
lean_dec(v_a_3710_);
lean_dec_ref(v_e_3699_);
return v___y_3715_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_inc(v_a_3716_);
lean_dec_ref_known(v___y_3715_, 1);
v___x_3718_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3719_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3718_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3731_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3731_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3731_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
uint8_t v___x_3724_; 
v___x_3724_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3720_, v_e_3699_);
lean_dec_ref(v_e_3699_);
lean_dec(v_a_3720_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3726_; 
lean_dec(v_a_3710_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_a_3716_);
v___x_3726_ = v___x_3722_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3716_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
else
{
lean_object* v___x_3729_; 
lean_dec(v_a_3716_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_a_3710_);
v___x_3729_ = v___x_3722_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3710_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3716_);
lean_dec(v_a_3710_);
lean_dec_ref(v_e_3699_);
v_a_3732_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3719_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3719_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
else
{
lean_dec(v_a_3710_);
lean_dec_ref(v_e_3699_);
return v___y_3715_;
}
}
}
}
else
{
lean_dec_ref(v_e_3699_);
return v___x_3709_;
}
}
else
{
uint8_t v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_dec_ref(v_e_3699_);
v___x_3760_ = 0;
v___x_3761_ = lean_box(v___x_3760_);
v___x_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
return v___x_3762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
lean_object* v_ref_3786_; uint8_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_ref_3786_ = lean_ctor_get(v_a_3784_, 2);
v___x_3787_ = 0;
v___x_3788_ = l_Lean_SourceInfo_fromRef(v_ref_3786_, v___x_3787_);
v___x_3789_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3790_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3788_);
v___x_3791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3788_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Lean_Syntax_node1(v___x_3788_, v___x_3789_, v___x_3791_);
v___x_3793_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3792_, v_a_3781_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v_a_3798_; lean_object* v___x_3799_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc_n(v_a_3794_, 2);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3795_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3781_);
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3781_);
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3796_, v_a_3794_, v_a_3798_, v_reason_3780_, v_a_3782_, v_a_3783_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; 
v_unused_3807_ = lean_ctor_get(v___x_3799_, 0);
lean_dec(v_unused_3807_);
v___x_3801_ = v___x_3799_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_dec(v___x_3799_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v_a_3794_);
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3794_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_a_3794_);
v_a_3808_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3799_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3799_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
return v___x_3793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec_ref(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_reason_3816_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3828_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_reason_3832_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
if (lean_obj_tag(v_x_3841_) == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3849_;
}
else
{
lean_object* v_head_3850_; lean_object* v_tail_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_head_3850_ = lean_ctor_get(v_x_3841_, 0);
lean_inc(v_head_3850_);
v_tail_3851_ = lean_ctor_get(v_x_3841_, 1);
lean_inc(v_tail_3851_);
lean_dec_ref_known(v_x_3841_, 2);
v___x_3852_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v___y_3847_);
lean_inc_ref(v___y_3846_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
v___x_3853_ = lean_apply_7(v_head_3850_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, lean_box(0));
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_dec(v_tail_3851_);
return v___x_3853_;
}
else
{
lean_object* v_a_3854_; uint8_t v___y_3856_; uint8_t v___x_3860_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
v___x_3860_ = l_Lean_Exception_isInterrupt(v_a_3854_);
if (v___x_3860_ == 0)
{
uint8_t v___x_3861_; 
lean_inc(v_a_3854_);
v___x_3861_ = l_Lean_Exception_isRuntime(v_a_3854_);
v___y_3856_ = v___x_3861_;
goto v___jp_3855_;
}
else
{
v___y_3856_ = v___x_3860_;
goto v___jp_3855_;
}
v___jp_3855_:
{
if (v___y_3856_ == 0)
{
if (lean_obj_tag(v_a_3854_) == 0)
{
lean_dec_ref_known(v_a_3854_, 2);
lean_dec(v_tail_3851_);
return v___x_3853_;
}
else
{
lean_object* v_id_3857_; uint8_t v___x_3858_; 
v_id_3857_ = lean_ctor_get(v_a_3854_, 0);
lean_inc(v_id_3857_);
lean_dec_ref_known(v_a_3854_, 2);
v___x_3858_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3852_, v_id_3857_);
lean_dec(v_id_3857_);
if (v___x_3858_ == 0)
{
lean_dec(v_tail_3851_);
return v___x_3853_;
}
else
{
lean_dec_ref_known(v___x_3853_, 1);
v_x_3841_ = v_tail_3851_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3854_);
lean_dec(v_tail_3851_);
return v___x_3853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
if (lean_obj_tag(v_x_3871_) == 0)
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3879_;
}
else
{
lean_object* v___x_3880_; lean_object* v___y_3882_; lean_object* v___y_3883_; uint8_t v___y_3884_; lean_object* v___y_3892_; lean_object* v___x_3896_; lean_object* v_env_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3880_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3896_ = lean_st_ref_get(v_a_3877_);
v_env_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_ref(v_env_3897_);
lean_dec(v___x_3896_);
v___x_3898_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3899_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3898_, v_env_3897_, v_x_3871_);
v___x_3900_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3899_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3901_, v_a_3872_, v_a_3873_, v_a_3874_);
v___y_3892_ = v___x_3902_;
goto v___jp_3891_;
}
else
{
v___y_3892_ = v___x_3900_;
goto v___jp_3891_;
}
v___jp_3881_:
{
if (v___y_3884_ == 0)
{
if (lean_obj_tag(v___y_3883_) == 0)
{
lean_dec_ref_known(v___y_3883_, 2);
lean_dec(v_x_3871_);
return v___y_3882_;
}
else
{
lean_object* v_id_3885_; uint8_t v___x_3886_; 
v_id_3885_ = lean_ctor_get(v___y_3883_, 0);
lean_inc(v_id_3885_);
lean_dec_ref_known(v___y_3883_, 2);
v___x_3886_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3880_, v_id_3885_);
lean_dec(v_id_3885_);
if (v___x_3886_ == 0)
{
lean_dec(v_x_3871_);
return v___y_3882_;
}
else
{
uint8_t v___x_3887_; 
lean_dec_ref(v___y_3882_);
v___x_3887_ = l_Lean_Name_isAtomic(v_x_3871_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_Name_getRoot(v_x_3871_);
lean_dec(v_x_3871_);
v_x_3871_ = v___x_3888_;
goto _start;
}
else
{
lean_object* v___x_3890_; 
lean_dec(v_x_3871_);
v___x_3890_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3890_;
}
}
}
}
else
{
lean_dec_ref(v___y_3883_);
lean_dec(v_x_3871_);
return v___y_3882_;
}
}
v___jp_3891_:
{
if (lean_obj_tag(v___y_3892_) == 0)
{
lean_dec(v_x_3871_);
return v___y_3892_;
}
else
{
lean_object* v_a_3893_; uint8_t v___x_3894_; 
v_a_3893_ = lean_ctor_get(v___y_3892_, 0);
lean_inc(v_a_3893_);
v___x_3894_ = l_Lean_Exception_isInterrupt(v_a_3893_);
if (v___x_3894_ == 0)
{
uint8_t v___x_3895_; 
lean_inc(v_a_3893_);
v___x_3895_ = l_Lean_Exception_isRuntime(v_a_3893_);
v___y_3882_ = v___y_3892_;
v___y_3883_ = v_a_3893_;
v___y_3884_ = v___x_3895_;
goto v___jp_3881_;
}
else
{
v___y_3882_ = v___y_3892_;
v___y_3883_ = v_a_3893_;
v___y_3884_ = v___x_3894_;
goto v___jp_3881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___x_3918_; lean_object* v_env_3919_; lean_object* v___x_3920_; lean_object* v_toCold_3921_; lean_object* v_mctx_3922_; lean_object* v_lctx_3923_; lean_object* v_options_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3918_ = lean_st_ref_get(v___y_3916_);
v_env_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc_ref(v_env_3919_);
lean_dec(v___x_3918_);
v___x_3920_ = lean_st_ref_get(v___y_3914_);
v_toCold_3921_ = lean_ctor_get(v___y_3915_, 0);
v_mctx_3922_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_mctx_3922_);
lean_dec(v___x_3920_);
v_lctx_3923_ = lean_ctor_get(v___y_3913_, 2);
v_options_3924_ = lean_ctor_get(v_toCold_3921_, 2);
lean_inc_ref(v_options_3924_);
lean_inc_ref(v_lctx_3923_);
v___x_3925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3925_, 0, v_env_3919_);
lean_ctor_set(v___x_3925_, 1, v_mctx_3922_);
lean_ctor_set(v___x_3925_, 2, v_lctx_3923_);
lean_ctor_set(v___x_3925_, 3, v_options_3924_);
v___x_3926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
lean_ctor_set(v___x_3926_, 1, v_msgData_3912_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_ref_3941_; lean_object* v___x_3942_; lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3951_; 
v_ref_3941_ = lean_ctor_get(v___y_3938_, 2);
v___x_3942_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
lean_inc(v_ref_3941_);
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_ref_3941_);
lean_ctor_set(v___x_3947_, 1, v_a_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set_tag(v___x_3945_, 1);
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
return v_res_3958_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_3962_);
v___x_3971_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_dec(v_a_3962_);
return v___x_3971_;
}
else
{
lean_object* v_a_3972_; uint8_t v___y_3974_; uint8_t v___x_3990_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
v___x_3990_ = l_Lean_Exception_isInterrupt(v_a_3972_);
if (v___x_3990_ == 0)
{
uint8_t v___x_3991_; 
lean_inc(v_a_3972_);
v___x_3991_ = l_Lean_Exception_isRuntime(v_a_3972_);
v___y_3974_ = v___x_3991_;
goto v___jp_3973_;
}
else
{
v___y_3974_ = v___x_3990_;
goto v___jp_3973_;
}
v___jp_3973_:
{
if (v___y_3974_ == 0)
{
if (lean_obj_tag(v_a_3972_) == 0)
{
lean_dec_ref_known(v_a_3972_, 2);
lean_dec(v_a_3962_);
return v___x_3971_;
}
else
{
lean_object* v_id_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3988_; 
v_id_3975_ = lean_ctor_get(v_a_3972_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_a_3972_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v_a_3972_, 1);
lean_dec(v_unused_3989_);
v___x_3977_ = v_a_3972_;
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_id_3975_);
lean_dec(v_a_3972_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
uint8_t v___x_3979_; 
v___x_3979_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3970_, v_id_3975_);
lean_dec(v_id_3975_);
if (v___x_3979_ == 0)
{
lean_del_object(v___x_3977_);
lean_dec(v_a_3962_);
return v___x_3971_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
lean_dec_ref_known(v___x_3971_, 1);
v___x_3980_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_3981_ = l_Lean_MessageData_ofName(v_a_3962_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 7);
lean_ctor_set(v___x_3977_, 1, v___x_3981_);
lean_ctor_set(v___x_3977_, 0, v___x_3980_);
v___x_3983_ = v___x_3977_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_3985_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3986_;
}
}
}
}
}
else
{
lean_dec(v_a_3972_);
lean_dec(v_a_3962_);
return v___x_3971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4011_; 
v___x_4009_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4002_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
lean_inc(v___y_4007_);
lean_inc_ref(v___y_4006_);
lean_inc(v___y_4005_);
lean_inc_ref(v___y_4004_);
v___x_4011_ = lean_infer_type(v_a_4010_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v___x_4013_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4014_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4012_, v___x_4013_, v_x_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4014_;
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v_x_4001_);
v_a_4015_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4011_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4011_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4031_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4050_ = l_String_toRawSubstring_x27(v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4109_ = l_Lean_Core_checkSystem(v___x_4108_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec_ref_known(v___x_4109_, 1);
v___x_4110_ = lean_st_ref_get(v_a_4102_);
v___x_4111_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4112_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4111_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_steps_4114_; uint8_t v___x_4115_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v_steps_4114_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_steps_4114_);
lean_dec(v___x_4110_);
v___x_4115_ = lean_nat_dec_le(v_a_4113_, v_steps_4114_);
lean_dec(v_steps_4114_);
lean_dec(v_a_4113_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; lean_object* v_steps_4117_; lean_object* v_infos_4118_; lean_object* v_holeIter_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4292_; 
v___x_4116_ = lean_st_ref_take(v_a_4102_);
v_steps_4117_ = lean_ctor_get(v___x_4116_, 0);
v_infos_4118_ = lean_ctor_get(v___x_4116_, 1);
v_holeIter_4119_ = lean_ctor_get(v___x_4116_, 2);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4121_ = v___x_4116_;
v_isShared_4122_ = v_isSharedCheck_4292_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_holeIter_4119_);
lean_inc(v_infos_4118_);
lean_inc(v_steps_4117_);
lean_dec(v___x_4116_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4292_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4123_ = lean_unsigned_to_nat(1u);
v___x_4124_ = lean_nat_add(v_steps_4117_, v___x_4123_);
lean_dec(v_steps_4117_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4124_);
v___x_4126_ = v___x_4121_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_infos_4118_);
lean_ctor_set(v_reuseFailAlloc_4291_, 2, v_holeIter_4119_);
v___x_4126_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_st_ref_put(v_a_4102_, v___x_4126_);
v___x_4128_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4101_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4130_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v___x_4130_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4129_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; uint8_t v___x_4132_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = lean_unbox(v_a_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
lean_inc(v_a_4129_);
v___x_4133_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4129_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; uint8_t v___x_4135_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v___x_4133_, 1);
v___x_4135_ = lean_unbox(v_a_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; 
lean_dec(v_a_4131_);
v___x_4136_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4138_, 0, v_a_4137_);
v___x_4139_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4138_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___y_4142_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___x_4189_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4190_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4189_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; uint8_t v___x_4192_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
v___x_4192_ = lean_unbox(v_a_4191_);
lean_dec(v_a_4191_);
if (v___x_4192_ == 0)
{
lean_dec(v_a_4129_);
v___y_4142_ = v___x_4190_;
goto v___jp_4141_;
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec_ref_known(v___x_4190_, 1);
v___x_4193_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4194_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4193_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; uint8_t v___x_4196_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
v___x_4196_ = lean_unbox(v_a_4195_);
lean_dec(v_a_4195_);
if (v___x_4196_ == 0)
{
lean_dec(v_a_4129_);
v___y_4142_ = v___x_4194_;
goto v___jp_4141_;
}
else
{
uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_Expr_isMData(v_a_4129_);
lean_dec(v_a_4129_);
if (v___x_4197_ == 0)
{
v___y_4142_ = v___x_4194_;
goto v___jp_4141_;
}
else
{
lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_a_4134_);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v___x_4194_, 0);
lean_dec(v_unused_4205_);
v___x_4199_ = v___x_4194_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_dec(v___x_4194_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_a_4140_);
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4140_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
else
{
lean_dec(v_a_4129_);
v___y_4142_ = v___x_4194_;
goto v___jp_4141_;
}
}
}
else
{
lean_dec(v_a_4129_);
v___y_4142_ = v___x_4190_;
goto v___jp_4141_;
}
v___jp_4141_:
{
if (lean_obj_tag(v___y_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4180_; 
v_a_4143_ = lean_ctor_get(v___y_4142_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___y_4142_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4145_ = v___y_4142_;
v_isShared_4146_ = v_isSharedCheck_4180_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___y_4142_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4180_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
uint8_t v___x_4147_; 
v___x_4147_ = lean_unbox(v_a_4143_);
lean_dec(v_a_4143_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4149_; 
lean_dec(v_a_4134_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v_a_4140_);
v___x_4149_ = v___x_4145_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4140_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_del_object(v___x_4145_);
v___x_4151_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4152_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4151_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_toCold_4153_; lean_object* v_a_4154_; lean_object* v_ref_4155_; lean_object* v_quotContext_4156_; lean_object* v_currMacroScope_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_toCold_4153_ = lean_ctor_get(v_a_4105_, 0);
v_a_4154_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4152_, 1);
v_ref_4155_ = lean_ctor_get(v_a_4105_, 2);
v_quotContext_4156_ = lean_ctor_get(v_toCold_4153_, 8);
v_currMacroScope_4157_ = lean_ctor_get(v_toCold_4153_, 9);
v___x_4158_ = lean_unbox(v_a_4134_);
lean_dec(v_a_4134_);
v___x_4159_ = l_Lean_SourceInfo_fromRef(v_ref_4155_, v___x_4158_);
v___x_4160_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4161_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4162_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4159_, 7);
v___x_4163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4159_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4165_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4166_ = lean_box(0);
lean_inc(v_currMacroScope_4157_);
lean_inc(v_quotContext_4156_);
v___x_4167_ = l_Lean_addMacroScope(v_quotContext_4156_, v___x_4166_, v_currMacroScope_4157_);
v___x_4168_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4169_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4159_);
lean_ctor_set(v___x_4169_, 1, v___x_4165_);
lean_ctor_set(v___x_4169_, 2, v___x_4167_);
lean_ctor_set(v___x_4169_, 3, v___x_4168_);
v___x_4170_ = l_Lean_Syntax_node1(v___x_4159_, v___x_4164_, v___x_4169_);
v___x_4171_ = l_Lean_Syntax_node2(v___x_4159_, v___x_4161_, v___x_4163_, v___x_4170_);
v___x_4172_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4159_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4175_ = l_Lean_Syntax_node1(v___x_4159_, v___x_4174_, v_a_4154_);
v___x_4176_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4159_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_Syntax_node5(v___x_4159_, v___x_4160_, v___x_4171_, v_a_4140_, v___x_4173_, v___x_4175_, v___x_4177_);
v___x_4179_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4178_, v_a_4101_);
return v___x_4179_;
}
else
{
lean_dec(v_a_4140_);
lean_dec(v_a_4134_);
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v_a_4140_);
lean_dec(v_a_4134_);
v_a_4181_ = lean_ctor_get(v___y_4142_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___y_4142_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___y_4142_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___y_4142_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
else
{
lean_dec(v_a_4134_);
lean_dec(v_a_4129_);
return v___x_4139_;
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec(v_a_4134_);
lean_dec(v_a_4129_);
v_a_4206_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4136_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4136_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec(v_a_4134_);
lean_dec(v_a_4129_);
v___x_4214_ = lean_box(1);
v___x_4215_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4214_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4105_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4218_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4217_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4256_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4256_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4256_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_unbox(v_a_4219_);
lean_dec(v_a_4219_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4225_; 
lean_dec(v_a_4131_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v_a_4216_);
v___x_4225_ = v___x_4221_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4216_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_del_object(v___x_4221_);
v___x_4227_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4228_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4227_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_toCold_4229_; lean_object* v_a_4230_; lean_object* v_ref_4231_; lean_object* v_quotContext_4232_; lean_object* v_currMacroScope_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_toCold_4229_ = lean_ctor_get(v_a_4105_, 0);
v_a_4230_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4228_, 1);
v_ref_4231_ = lean_ctor_get(v_a_4105_, 2);
v_quotContext_4232_ = lean_ctor_get(v_toCold_4229_, 8);
v_currMacroScope_4233_ = lean_ctor_get(v_toCold_4229_, 9);
v___x_4234_ = lean_unbox(v_a_4131_);
lean_dec(v_a_4131_);
v___x_4235_ = l_Lean_SourceInfo_fromRef(v_ref_4231_, v___x_4234_);
v___x_4236_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4237_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4238_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4235_, 7);
v___x_4239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4235_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4241_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4242_ = lean_box(0);
lean_inc(v_currMacroScope_4233_);
lean_inc(v_quotContext_4232_);
v___x_4243_ = l_Lean_addMacroScope(v_quotContext_4232_, v___x_4242_, v_currMacroScope_4233_);
v___x_4244_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4245_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4235_);
lean_ctor_set(v___x_4245_, 1, v___x_4241_);
lean_ctor_set(v___x_4245_, 2, v___x_4243_);
lean_ctor_set(v___x_4245_, 3, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node1(v___x_4235_, v___x_4240_, v___x_4245_);
v___x_4247_ = l_Lean_Syntax_node2(v___x_4235_, v___x_4237_, v___x_4239_, v___x_4246_);
v___x_4248_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4235_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4251_ = l_Lean_Syntax_node1(v___x_4235_, v___x_4250_, v_a_4230_);
v___x_4252_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4235_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = l_Lean_Syntax_node5(v___x_4235_, v___x_4236_, v___x_4247_, v_a_4216_, v___x_4249_, v___x_4251_, v___x_4253_);
v___x_4255_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4254_, v_a_4101_);
return v___x_4255_;
}
else
{
lean_dec(v_a_4216_);
lean_dec(v_a_4131_);
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec(v_a_4216_);
lean_dec(v_a_4131_);
v_a_4257_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4218_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4218_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_dec(v_a_4131_);
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_a_4131_);
lean_dec(v_a_4129_);
v_a_4265_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4133_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4133_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec(v_a_4131_);
lean_dec(v_a_4129_);
v___x_4273_ = lean_box(0);
v___x_4274_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4273_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4105_);
return v___x_4274_;
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_a_4129_);
v_a_4275_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4130_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4130_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4128_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4128_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
else
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_box(2);
v___x_4294_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4293_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4105_);
return v___x_4294_;
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec(v___x_4110_);
v_a_4295_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4112_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4112_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_a_4303_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4109_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4109_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4311_, lean_object* v_msg_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4319_, lean_object* v_msg_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4319_, v_msg_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4327_, lean_object* v_x_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4337_, lean_object* v_x_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4337_, v_x_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4348_, lean_object* v_prec_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4357_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4358_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4357_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4371_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4371_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4371_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; lean_object* v_mctx_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4363_ = lean_st_ref_get(v_a_4353_);
v_mctx_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc_ref(v_mctx_4364_);
lean_dec(v___x_4363_);
v___x_4365_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4365_, 0, v_mctx_4364_);
v___x_4366_ = lean_unbox(v_a_4359_);
lean_dec(v_a_4359_);
v___x_4367_ = l_Lean_Level_quote(v_l_4348_, v_prec_4349_, v___x_4366_, v___x_4365_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4367_);
v___x_4369_ = v___x_4361_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_l_4348_);
v_a_4372_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4358_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4358_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4380_, lean_object* v_prec_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4380_, v_prec_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_prec_4381_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4390_, lean_object* v_stx_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___x_4397_ = lean_box(0);
v___x_4398_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4396_, v___x_4397_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_n(v_a_4399_, 2);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = 0;
v___x_4401_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_a_4399_, v___x_4400_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v___x_4401_, 0);
lean_dec(v_unused_4409_);
v___x_4403_ = v___x_4401_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_dec(v___x_4401_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_a_4399_);
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4399_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_a_4399_);
v_a_4410_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4401_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4401_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
return v___x_4398_;
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
v_a_4418_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4395_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4395_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4426_, lean_object* v_stx_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_x_410__boxed_4431_; lean_object* v_res_4432_; 
v_x_410__boxed_4431_ = lean_unbox(v_x_4426_);
v_res_4432_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_410__boxed_4431_, v_stx_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4458_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4459_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4457_, v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4465_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4466_ = l_Lean_addBuiltinDocString(v___x_4464_, v___x_4465_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4496_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4497_ = l_Lean_addBuiltinDeclarationRanges(v___x_4495_, v___x_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v___x_4503_; lean_object* v_mctx_4504_; lean_object* v___x_4505_; lean_object* v_fst_4506_; lean_object* v_snd_4507_; lean_object* v___x_4508_; lean_object* v_cache_4509_; lean_object* v_zetaDeltaFVarIds_4510_; lean_object* v_postponed_4511_; lean_object* v_diag_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4521_; 
v___x_4503_ = lean_st_ref_get(v___y_4501_);
v_mctx_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc_ref(v_mctx_4504_);
lean_dec(v___x_4503_);
v___x_4505_ = lean_instantiate_level_mvars(v_mctx_4504_, v_l_4500_);
v_fst_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_fst_4506_);
v_snd_4507_ = lean_ctor_get(v___x_4505_, 1);
lean_inc(v_snd_4507_);
lean_dec_ref(v___x_4505_);
v___x_4508_ = lean_st_ref_take(v___y_4501_);
v_cache_4509_ = lean_ctor_get(v___x_4508_, 1);
v_zetaDeltaFVarIds_4510_ = lean_ctor_get(v___x_4508_, 2);
v_postponed_4511_ = lean_ctor_get(v___x_4508_, 3);
v_diag_4512_ = lean_ctor_get(v___x_4508_, 4);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4521_ == 0)
{
lean_object* v_unused_4522_; 
v_unused_4522_ = lean_ctor_get(v___x_4508_, 0);
lean_dec(v_unused_4522_);
v___x_4514_ = v___x_4508_;
v_isShared_4515_ = v_isSharedCheck_4521_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_diag_4512_);
lean_inc(v_postponed_4511_);
lean_inc(v_zetaDeltaFVarIds_4510_);
lean_inc(v_cache_4509_);
lean_dec(v___x_4508_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4521_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v_fst_4506_);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_fst_4506_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_cache_4509_);
lean_ctor_set(v_reuseFailAlloc_4520_, 2, v_zetaDeltaFVarIds_4510_);
lean_ctor_set(v_reuseFailAlloc_4520_, 3, v_postponed_4511_);
lean_ctor_set(v_reuseFailAlloc_4520_, 4, v_diag_4512_);
v___x_4517_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = lean_st_ref_put(v___y_4501_, v___x_4517_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v_snd_4507_);
return v___x_4519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4523_, v___y_4524_);
lean_dec(v___y_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4527_, v___y_4529_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4541_, lean_object* v_prec_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_l_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___x_4559_; uint8_t v___x_4560_; 
v___x_4559_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4545_);
v___x_4560_ = l_Lean_getPPInstantiateMVars(v___x_4559_);
lean_dec_ref(v___x_4559_);
if (v___x_4560_ == 0)
{
v_l_4549_ = v_l_4541_;
v___y_4550_ = v_a_4544_;
v___y_4551_ = v_a_4545_;
goto v___jp_4548_;
}
else
{
lean_object* v___x_4561_; lean_object* v_a_4562_; 
v___x_4561_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4541_, v_a_4544_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4561_);
v_l_4549_ = v_a_4562_;
v___y_4550_ = v_a_4544_;
v___y_4551_ = v_a_4545_;
goto v___jp_4548_;
}
v___jp_4548_:
{
lean_object* v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v_mctx_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4552_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4551_);
v___x_4553_ = l_Lean_getPPMVarsLevels(v___x_4552_);
lean_dec_ref(v___x_4552_);
v___x_4554_ = lean_st_ref_get(v___y_4550_);
v_mctx_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc_ref(v_mctx_4555_);
lean_dec(v___x_4554_);
v___x_4556_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4556_, 0, v_mctx_4555_);
v___x_4557_ = l_Lean_Level_quote(v_l_4549_, v_prec_4542_, v___x_4553_, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4563_, lean_object* v_prec_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_PrettyPrinter_delabLevel(v_l_4563_, v_prec_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_prec_4564_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___f_4578_; lean_object* v___x_8060__overap_4579_; lean_object* v___x_4580_; 
v___f_4578_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8060__overap_4579_ = lean_panic_fn_borrowed(v___f_4578_, v_msg_4572_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc(v___y_4574_);
lean_inc_ref(v___y_4573_);
v___x_4580_ = lean_apply_5(v___x_8060__overap_4579_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, lean_box(0));
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4588_, lean_object* v_msg_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4596_, lean_object* v_msg_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4596_, v_msg_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4604_, lean_object* v_opt_4605_){
_start:
{
lean_object* v_name_4606_; lean_object* v_defValue_4607_; lean_object* v_map_4608_; lean_object* v___x_4609_; 
v_name_4606_ = lean_ctor_get(v_opt_4605_, 0);
v_defValue_4607_ = lean_ctor_get(v_opt_4605_, 1);
v_map_4608_ = lean_ctor_get(v_opts_4604_, 0);
v___x_4609_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4608_, v_name_4606_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_inc(v_defValue_4607_);
return v_defValue_4607_;
}
else
{
lean_object* v_val_4610_; 
v_val_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_val_4610_);
lean_dec_ref_known(v___x_4609_, 1);
if (lean_obj_tag(v_val_4610_) == 3)
{
lean_object* v_v_4611_; 
v_v_4611_ = lean_ctor_get(v_val_4610_, 0);
lean_inc(v_v_4611_);
lean_dec_ref_known(v_val_4610_, 1);
return v_v_4611_;
}
else
{
lean_dec(v_val_4610_);
lean_inc(v_defValue_4607_);
return v_defValue_4607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4612_, lean_object* v_opt_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4612_, v_opt_4613_);
lean_dec_ref(v_opt_4613_);
lean_dec_ref(v_opts_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(lean_object* v_e_4615_, lean_object* v___y_4616_){
_start:
{
uint8_t v___x_4618_; 
v___x_4618_ = l_Lean_Expr_hasMVar(v_e_4615_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v_e_4615_);
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; lean_object* v_mctx_4621_; lean_object* v___x_4622_; lean_object* v_fst_4623_; lean_object* v_snd_4624_; lean_object* v___x_4625_; lean_object* v_cache_4626_; lean_object* v_zetaDeltaFVarIds_4627_; lean_object* v_postponed_4628_; lean_object* v_diag_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4638_; 
v___x_4620_ = lean_st_ref_get(v___y_4616_);
v_mctx_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc_ref(v_mctx_4621_);
lean_dec(v___x_4620_);
v___x_4622_ = l_Lean_instantiateMVarsCore(v_mctx_4621_, v_e_4615_);
v_fst_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_fst_4623_);
v_snd_4624_ = lean_ctor_get(v___x_4622_, 1);
lean_inc(v_snd_4624_);
lean_dec_ref(v___x_4622_);
v___x_4625_ = lean_st_ref_take(v___y_4616_);
v_cache_4626_ = lean_ctor_get(v___x_4625_, 1);
v_zetaDeltaFVarIds_4627_ = lean_ctor_get(v___x_4625_, 2);
v_postponed_4628_ = lean_ctor_get(v___x_4625_, 3);
v_diag_4629_ = lean_ctor_get(v___x_4625_, 4);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4638_ == 0)
{
lean_object* v_unused_4639_; 
v_unused_4639_ = lean_ctor_get(v___x_4625_, 0);
lean_dec(v_unused_4639_);
v___x_4631_ = v___x_4625_;
v_isShared_4632_ = v_isSharedCheck_4638_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_diag_4629_);
lean_inc(v_postponed_4628_);
lean_inc(v_zetaDeltaFVarIds_4627_);
lean_inc(v_cache_4626_);
lean_dec(v___x_4625_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4638_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v_snd_4624_);
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_snd_4624_);
lean_ctor_set(v_reuseFailAlloc_4637_, 1, v_cache_4626_);
lean_ctor_set(v_reuseFailAlloc_4637_, 2, v_zetaDeltaFVarIds_4627_);
lean_ctor_set(v_reuseFailAlloc_4637_, 3, v_postponed_4628_);
lean_ctor_set(v_reuseFailAlloc_4637_, 4, v_diag_4629_);
v___x_4634_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_st_ref_put(v___y_4616_, v___x_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v_fst_4623_);
return v___x_4636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg___boxed(lean_object* v_e_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4640_, v___y_4641_);
lean_dec(v___y_4641_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_e_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4644_, v___y_4646_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_e_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(v_e_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4658_, lean_object* v_opt_4659_){
_start:
{
lean_object* v_name_4660_; lean_object* v_map_4661_; lean_object* v___x_4662_; 
v_name_4660_ = lean_ctor_get(v_opt_4659_, 0);
v_map_4661_ = lean_ctor_get(v_opts_4658_, 0);
v___x_4662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4661_, v_name_4660_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v___x_4663_; 
v___x_4663_ = lean_box(0);
return v___x_4663_;
}
else
{
lean_object* v_val_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4674_; 
v_val_4664_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4666_ = v___x_4662_;
v_isShared_4667_ = v_isSharedCheck_4674_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_val_4664_);
lean_dec(v___x_4662_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4674_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
if (lean_obj_tag(v_val_4664_) == 1)
{
uint8_t v_v_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v_v_4668_ = lean_ctor_get_uint8(v_val_4664_, 0);
lean_dec_ref_known(v_val_4664_, 0);
v___x_4669_ = lean_box(v_v_4668_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v___x_4669_);
v___x_4671_ = v___x_4666_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
else
{
lean_object* v___x_4673_; 
lean_del_object(v___x_4666_);
lean_dec(v_val_4664_);
v___x_4673_ = lean_box(0);
return v___x_4673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4675_, lean_object* v_opt_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4675_, v_opt_4676_);
lean_dec_ref(v_opt_4676_);
lean_dec_ref(v_opts_4675_);
return v_res_4677_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_x_4678_, lean_object* v_x_4679_){
_start:
{
if (lean_obj_tag(v_x_4678_) == 0)
{
if (lean_obj_tag(v_x_4679_) == 0)
{
uint8_t v___x_4680_; 
v___x_4680_ = 1;
return v___x_4680_;
}
else
{
uint8_t v___x_4681_; 
v___x_4681_ = 0;
return v___x_4681_;
}
}
else
{
if (lean_obj_tag(v_x_4679_) == 0)
{
uint8_t v___x_4682_; 
v___x_4682_ = 0;
return v___x_4682_;
}
else
{
lean_object* v_val_4683_; uint8_t v___x_4684_; 
v_val_4683_ = lean_ctor_get(v_x_4679_, 0);
v___x_4684_ = lean_unbox(v_val_4683_);
if (v___x_4684_ == 0)
{
lean_object* v_val_4685_; uint8_t v___x_4686_; 
v_val_4685_ = lean_ctor_get(v_x_4678_, 0);
v___x_4686_ = lean_unbox(v_val_4685_);
if (v___x_4686_ == 0)
{
uint8_t v___x_4687_; 
v___x_4687_ = 1;
return v___x_4687_;
}
else
{
uint8_t v___x_4688_; 
v___x_4688_ = lean_unbox(v_val_4683_);
return v___x_4688_;
}
}
else
{
lean_object* v_val_4689_; uint8_t v___x_4690_; 
v_val_4689_ = lean_ctor_get(v_x_4678_, 0);
v___x_4690_ = lean_unbox(v_val_4689_);
return v___x_4690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_x_4691_, lean_object* v_x_4692_){
_start:
{
uint8_t v_res_4693_; lean_object* v_r_4694_; 
v_res_4693_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(v_x_4691_, v_x_4692_);
lean_dec(v_x_4692_);
lean_dec(v_x_4691_);
v_r_4694_ = lean_box(v_res_4693_);
return v_r_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_cls_4695_, lean_object* v_msg_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_ref_4702_; lean_object* v___x_4703_; lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4749_; 
v_ref_4702_ = lean_ctor_get(v___y_4699_, 2);
v___x_4703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4749_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4749_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v_traceState_4709_; lean_object* v_env_4710_; lean_object* v_nextMacroScope_4711_; lean_object* v_ngen_4712_; lean_object* v_auxDeclNGen_4713_; lean_object* v_cache_4714_; lean_object* v_recordedDeps_4715_; lean_object* v_messages_4716_; lean_object* v_infoState_4717_; lean_object* v_snapshotTasks_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4748_; 
v___x_4708_ = lean_st_ref_take(v___y_4700_);
v_traceState_4709_ = lean_ctor_get(v___x_4708_, 4);
v_env_4710_ = lean_ctor_get(v___x_4708_, 0);
v_nextMacroScope_4711_ = lean_ctor_get(v___x_4708_, 1);
v_ngen_4712_ = lean_ctor_get(v___x_4708_, 2);
v_auxDeclNGen_4713_ = lean_ctor_get(v___x_4708_, 3);
v_cache_4714_ = lean_ctor_get(v___x_4708_, 5);
v_recordedDeps_4715_ = lean_ctor_get(v___x_4708_, 6);
v_messages_4716_ = lean_ctor_get(v___x_4708_, 7);
v_infoState_4717_ = lean_ctor_get(v___x_4708_, 8);
v_snapshotTasks_4718_ = lean_ctor_get(v___x_4708_, 9);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4720_ = v___x_4708_;
v_isShared_4721_ = v_isSharedCheck_4748_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_snapshotTasks_4718_);
lean_inc(v_infoState_4717_);
lean_inc(v_messages_4716_);
lean_inc(v_recordedDeps_4715_);
lean_inc(v_cache_4714_);
lean_inc(v_traceState_4709_);
lean_inc(v_auxDeclNGen_4713_);
lean_inc(v_ngen_4712_);
lean_inc(v_nextMacroScope_4711_);
lean_inc(v_env_4710_);
lean_dec(v___x_4708_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4748_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
uint64_t v_tid_4722_; lean_object* v_traces_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4747_; 
v_tid_4722_ = lean_ctor_get_uint64(v_traceState_4709_, sizeof(void*)*1);
v_traces_4723_ = lean_ctor_get(v_traceState_4709_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_traceState_4709_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4725_ = v_traceState_4709_;
v_isShared_4726_ = v_isSharedCheck_4747_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_traces_4723_);
lean_dec(v_traceState_4709_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4747_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; double v___x_4729_; uint8_t v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
v___x_4727_ = lean_box(0);
v___x_4728_ = lean_box(0);
v___x_4729_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_4730_ = 0;
v___x_4731_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4732_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4732_, 0, v_cls_4695_);
lean_ctor_set(v___x_4732_, 1, v___x_4728_);
lean_ctor_set(v___x_4732_, 2, v___x_4731_);
lean_ctor_set_float(v___x_4732_, sizeof(void*)*3, v___x_4729_);
lean_ctor_set_float(v___x_4732_, sizeof(void*)*3 + 8, v___x_4729_);
lean_ctor_set_uint8(v___x_4732_, sizeof(void*)*3 + 16, v___x_4730_);
v___x_4733_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_4734_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v_a_4704_);
lean_ctor_set(v___x_4734_, 2, v___x_4733_);
lean_inc(v_ref_4702_);
v___x_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4735_, 0, v_ref_4702_);
lean_ctor_set(v___x_4735_, 1, v___x_4734_);
v___x_4736_ = l_Lean_PersistentArray_push___redArg(v_traces_4723_, v___x_4735_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 0, v___x_4736_);
v___x_4738_ = v___x_4725_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4736_);
lean_ctor_set_uint64(v_reuseFailAlloc_4746_, sizeof(void*)*1, v_tid_4722_);
v___x_4738_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4740_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 4, v___x_4738_);
v___x_4740_ = v___x_4720_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_env_4710_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_nextMacroScope_4711_);
lean_ctor_set(v_reuseFailAlloc_4745_, 2, v_ngen_4712_);
lean_ctor_set(v_reuseFailAlloc_4745_, 3, v_auxDeclNGen_4713_);
lean_ctor_set(v_reuseFailAlloc_4745_, 4, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4745_, 5, v_cache_4714_);
lean_ctor_set(v_reuseFailAlloc_4745_, 6, v_recordedDeps_4715_);
lean_ctor_set(v_reuseFailAlloc_4745_, 7, v_messages_4716_);
lean_ctor_set(v_reuseFailAlloc_4745_, 8, v_infoState_4717_);
lean_ctor_set(v_reuseFailAlloc_4745_, 9, v_snapshotTasks_4718_);
v___x_4740_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4741_ = lean_st_ref_put(v___y_4700_, v___x_4740_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4727_);
v___x_4743_ = v___x_4706_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4727_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_cls_4750_, lean_object* v_msg_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v_cls_4750_, v_msg_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(lean_object* v_o_4758_, lean_object* v_k_4759_, uint8_t v_v_4760_){
_start:
{
lean_object* v_map_4761_; uint8_t v_hasTrace_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4776_; 
v_map_4761_ = lean_ctor_get(v_o_4758_, 0);
v_hasTrace_4762_ = lean_ctor_get_uint8(v_o_4758_, sizeof(void*)*1);
v_isSharedCheck_4776_ = !lean_is_exclusive(v_o_4758_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4764_ = v_o_4758_;
v_isShared_4765_ = v_isSharedCheck_4776_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_map_4761_);
lean_dec(v_o_4758_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4776_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4766_, 0, v_v_4760_);
lean_inc(v_k_4759_);
v___x_4767_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4759_, v___x_4766_, v_map_4761_);
if (v_hasTrace_4762_ == 0)
{
lean_object* v___x_4768_; uint8_t v___x_4769_; lean_object* v___x_4771_; 
v___x_4768_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4769_ = l_Lean_Name_isPrefixOf(v___x_4768_, v_k_4759_);
lean_dec(v_k_4759_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4767_);
v___x_4771_ = v___x_4764_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4767_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_ctor_set_uint8(v___x_4771_, sizeof(void*)*1, v___x_4769_);
return v___x_4771_;
}
}
else
{
lean_object* v___x_4774_; 
lean_dec(v_k_4759_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4767_);
v___x_4774_ = v___x_4764_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4767_);
lean_ctor_set_uint8(v_reuseFailAlloc_4775_, sizeof(void*)*1, v_hasTrace_4762_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3___boxed(lean_object* v_o_4777_, lean_object* v_k_4778_, lean_object* v_v_4779_){
_start:
{
uint8_t v_v_boxed_4780_; lean_object* v_res_4781_; 
v_v_boxed_4780_ = lean_unbox(v_v_4779_);
v_res_4781_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(v_o_4777_, v_k_4778_, v_v_boxed_4780_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_opts_4782_, lean_object* v_opt_4783_, uint8_t v_val_4784_){
_start:
{
lean_object* v_name_4785_; lean_object* v___x_4786_; 
v_name_4785_ = lean_ctor_get(v_opt_4783_, 0);
lean_inc(v_name_4785_);
lean_dec_ref(v_opt_4783_);
v___x_4786_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(v_opts_4782_, v_name_4785_, v_val_4784_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_opts_4787_, lean_object* v_opt_4788_, lean_object* v_val_4789_){
_start:
{
uint8_t v_val_boxed_4790_; lean_object* v_res_4791_; 
v_val_boxed_4790_ = lean_unbox(v_val_4789_);
v_res_4791_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(v_opts_4787_, v_opt_4788_, v_val_boxed_4790_);
return v_res_4791_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4795_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4796_ = lean_unsigned_to_nat(18u);
v___x_4797_ = lean_unsigned_to_nat(536u);
v___x_4798_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4799_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4800_ = l_mkPanicMessageWithDecl(v___x_4799_, v___x_4798_, v___x_4797_, v___x_4796_, v___x_4795_);
return v___x_4800_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4802_ = lean_unsigned_to_nat(2u);
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
lean_ctor_set(v___x_4803_, 1, v___x_4801_);
return v___x_4803_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4804_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4805_ = lean_box(1);
v___x_4806_ = lean_unsigned_to_nat(0u);
v___x_4807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
lean_ctor_set(v___x_4807_, 1, v___x_4805_);
lean_ctor_set(v___x_4807_, 2, v___x_4804_);
return v___x_4807_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4815_ = l_Lean_Name_append(v___x_4814_, v___x_4813_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4816_, lean_object* v_optionsPerPos_4817_, lean_object* v_delab_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_fst_4825_; lean_object* v_snd_4826_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; uint8_t v___y_4837_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v_optionsPerPos_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4889_; lean_object* v_e_4890_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v___y_4908_; lean_object* v_e_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___x_4925_; 
v___x_4925_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4816_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_5062_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_5062_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_5062_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___y_4931_; lean_object* v___y_4932_; uint8_t v___y_4933_; uint16_t v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4960_; lean_object* v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; uint16_t v___y_4964_; uint8_t v___y_4965_; uint8_t v___y_4966_; lean_object* v___y_4967_; lean_object* v_opts_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; uint8_t v___y_5013_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; uint8_t v___y_5024_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v_toCold_5043_; lean_object* v_options_5044_; uint8_t v_hasTrace_5045_; 
v_toCold_5043_ = lean_ctor_get(v_a_4821_, 0);
v_options_5044_ = lean_ctor_get(v_toCold_5043_, 2);
v_hasTrace_5045_ = lean_ctor_get_uint8(v_options_5044_, sizeof(void*)*1);
if (v_hasTrace_5045_ == 0)
{
v___y_5033_ = v_a_4819_;
v___y_5034_ = v_a_4820_;
v___y_5035_ = v_a_4821_;
v___y_5036_ = v_a_4822_;
goto v___jp_5032_;
}
else
{
lean_object* v_inheritedTraceOptions_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v_inheritedTraceOptions_5046_ = lean_ctor_get(v_toCold_5043_, 11);
v___x_5047_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5048_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5046_, v_options_5044_, v___x_5048_);
if (v___x_5049_ == 0)
{
v___y_5033_ = v_a_4819_;
v___y_5034_ = v_a_4820_;
v___y_5035_ = v_a_4821_;
v___y_5036_ = v_a_4822_;
goto v___jp_5032_;
}
else
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5050_ = lean_expr_dbg_to_string(v_a_4926_);
v___x_5051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
v___x_5052_ = l_Lean_MessageData_ofFormat(v___x_5051_);
v___x_5053_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5047_, v___x_5052_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_dec_ref_known(v___x_5053_, 1);
v___y_5033_ = v_a_4819_;
v___y_5034_ = v_a_4820_;
v___y_5035_ = v_a_4821_;
v___y_5036_ = v_a_4822_;
goto v___jp_5032_;
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_del_object(v___x_4928_);
lean_dec(v_a_4926_);
lean_dec_ref(v_delab_4818_);
lean_dec(v_optionsPerPos_4817_);
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
}
v___jp_4930_:
{
lean_object* v_toCold_4938_; lean_object* v_currRecDepth_4939_; lean_object* v_ref_4940_; uint8_t v_suppressElabErrors_4941_; uint8_t v_isRecordingDeps_4942_; lean_object* v_fileName_4943_; lean_object* v_fileMap_4944_; lean_object* v_currNamespace_4945_; lean_object* v_openDecls_4946_; lean_object* v_initHeartbeats_4947_; lean_object* v_maxHeartbeats_4948_; lean_object* v_quotContext_4949_; lean_object* v_currMacroScope_4950_; lean_object* v_cancelTk_x3f_4951_; lean_object* v_inheritedTraceOptions_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v_toCold_4938_ = lean_ctor_get(v___y_4936_, 0);
v_currRecDepth_4939_ = lean_ctor_get(v___y_4936_, 1);
v_ref_4940_ = lean_ctor_get(v___y_4936_, 2);
v_suppressElabErrors_4941_ = lean_ctor_get_uint8(v___y_4936_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4942_ = lean_ctor_get_uint8(v___y_4936_, sizeof(void*)*3 + 3);
v_fileName_4943_ = lean_ctor_get(v_toCold_4938_, 0);
v_fileMap_4944_ = lean_ctor_get(v_toCold_4938_, 1);
v_currNamespace_4945_ = lean_ctor_get(v_toCold_4938_, 4);
v_openDecls_4946_ = lean_ctor_get(v_toCold_4938_, 5);
v_initHeartbeats_4947_ = lean_ctor_get(v_toCold_4938_, 6);
v_maxHeartbeats_4948_ = lean_ctor_get(v_toCold_4938_, 7);
v_quotContext_4949_ = lean_ctor_get(v_toCold_4938_, 8);
v_currMacroScope_4950_ = lean_ctor_get(v_toCold_4938_, 9);
v_cancelTk_x3f_4951_ = lean_ctor_get(v_toCold_4938_, 10);
v_inheritedTraceOptions_4952_ = lean_ctor_get(v_toCold_4938_, 11);
v___x_4953_ = l_Lean_maxRecDepth;
v___x_4954_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v___y_4932_, v___x_4953_);
lean_inc_ref(v_inheritedTraceOptions_4952_);
lean_inc(v_cancelTk_x3f_4951_);
lean_inc(v_currMacroScope_4950_);
lean_inc(v_quotContext_4949_);
lean_inc(v_maxHeartbeats_4948_);
lean_inc(v_initHeartbeats_4947_);
lean_inc(v_openDecls_4946_);
lean_inc(v_currNamespace_4945_);
lean_inc_ref(v___y_4932_);
lean_inc_ref(v_fileMap_4944_);
lean_inc_ref(v_fileName_4943_);
v___x_4955_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4955_, 0, v_fileName_4943_);
lean_ctor_set(v___x_4955_, 1, v_fileMap_4944_);
lean_ctor_set(v___x_4955_, 2, v___y_4932_);
lean_ctor_set(v___x_4955_, 3, v___x_4954_);
lean_ctor_set(v___x_4955_, 4, v_currNamespace_4945_);
lean_ctor_set(v___x_4955_, 5, v_openDecls_4946_);
lean_ctor_set(v___x_4955_, 6, v_initHeartbeats_4947_);
lean_ctor_set(v___x_4955_, 7, v_maxHeartbeats_4948_);
lean_ctor_set(v___x_4955_, 8, v_quotContext_4949_);
lean_ctor_set(v___x_4955_, 9, v_currMacroScope_4950_);
lean_ctor_set(v___x_4955_, 10, v_cancelTk_x3f_4951_);
lean_ctor_set(v___x_4955_, 11, v_inheritedTraceOptions_4952_);
lean_inc(v_ref_4940_);
lean_inc(v_currRecDepth_4939_);
v___x_4956_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v_currRecDepth_4939_);
lean_ctor_set(v___x_4956_, 2, v_ref_4940_);
lean_ctor_set_uint16(v___x_4956_, sizeof(void*)*3, v___y_4934_);
lean_ctor_set_uint8(v___x_4956_, sizeof(void*)*3 + 2, v_suppressElabErrors_4941_);
lean_ctor_set_uint8(v___x_4956_, sizeof(void*)*3 + 3, v_isRecordingDeps_4942_);
if (v___y_4933_ == 0)
{
v___y_4908_ = v___y_4932_;
v_e_4909_ = v_a_4926_;
v___y_4910_ = v___y_4935_;
v___y_4911_ = v___y_4931_;
v___y_4912_ = v___x_4956_;
v___y_4913_ = v___y_4937_;
goto v___jp_4907_;
}
else
{
lean_object* v___x_4957_; lean_object* v_a_4958_; 
v___x_4957_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_a_4926_, v___y_4931_);
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref(v___x_4957_);
v___y_4908_ = v___y_4932_;
v_e_4909_ = v_a_4958_;
v___y_4910_ = v___y_4935_;
v___y_4911_ = v___y_4931_;
v___y_4912_ = v___x_4956_;
v___y_4913_ = v___y_4937_;
goto v___jp_4907_;
}
}
v___jp_4959_:
{
lean_object* v___x_4968_; lean_object* v_env_4969_; lean_object* v_nextMacroScope_4970_; lean_object* v_ngen_4971_; lean_object* v_auxDeclNGen_4972_; lean_object* v_traceState_4973_; lean_object* v_recordedDeps_4974_; lean_object* v_messages_4975_; lean_object* v_infoState_4976_; lean_object* v_snapshotTasks_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4987_; 
v___x_4968_ = lean_st_ref_take(v___y_4963_);
v_env_4969_ = lean_ctor_get(v___x_4968_, 0);
v_nextMacroScope_4970_ = lean_ctor_get(v___x_4968_, 1);
v_ngen_4971_ = lean_ctor_get(v___x_4968_, 2);
v_auxDeclNGen_4972_ = lean_ctor_get(v___x_4968_, 3);
v_traceState_4973_ = lean_ctor_get(v___x_4968_, 4);
v_recordedDeps_4974_ = lean_ctor_get(v___x_4968_, 6);
v_messages_4975_ = lean_ctor_get(v___x_4968_, 7);
v_infoState_4976_ = lean_ctor_get(v___x_4968_, 8);
v_snapshotTasks_4977_ = lean_ctor_get(v___x_4968_, 9);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_4987_ == 0)
{
lean_object* v_unused_4988_; 
v_unused_4988_ = lean_ctor_get(v___x_4968_, 5);
lean_dec(v_unused_4988_);
v___x_4979_ = v___x_4968_;
v_isShared_4980_ = v_isSharedCheck_4987_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_snapshotTasks_4977_);
lean_inc(v_infoState_4976_);
lean_inc(v_messages_4975_);
lean_inc(v_recordedDeps_4974_);
lean_inc(v_traceState_4973_);
lean_inc(v_auxDeclNGen_4972_);
lean_inc(v_ngen_4971_);
lean_inc(v_nextMacroScope_4970_);
lean_inc(v_env_4969_);
lean_dec(v___x_4968_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4987_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4981_ = l_Lean_Kernel_enableDiag(v_env_4969_, v___y_4966_);
v___x_4982_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 5, v___x_4982_);
lean_ctor_set(v___x_4979_, 0, v___x_4981_);
v___x_4984_ = v___x_4979_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4981_);
lean_ctor_set(v_reuseFailAlloc_4986_, 1, v_nextMacroScope_4970_);
lean_ctor_set(v_reuseFailAlloc_4986_, 2, v_ngen_4971_);
lean_ctor_set(v_reuseFailAlloc_4986_, 3, v_auxDeclNGen_4972_);
lean_ctor_set(v_reuseFailAlloc_4986_, 4, v_traceState_4973_);
lean_ctor_set(v_reuseFailAlloc_4986_, 5, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_4986_, 6, v_recordedDeps_4974_);
lean_ctor_set(v_reuseFailAlloc_4986_, 7, v_messages_4975_);
lean_ctor_set(v_reuseFailAlloc_4986_, 8, v_infoState_4976_);
lean_ctor_set(v_reuseFailAlloc_4986_, 9, v_snapshotTasks_4977_);
v___x_4984_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; 
v___x_4985_ = lean_st_ref_put(v___y_4963_, v___x_4984_);
v___y_4931_ = v___y_4961_;
v___y_4932_ = v___y_4960_;
v___y_4933_ = v___y_4965_;
v___y_4934_ = v___y_4964_;
v___y_4935_ = v___y_4967_;
v___y_4936_ = v___y_4962_;
v___y_4937_ = v___y_4963_;
goto v___jp_4930_;
}
}
}
v___jp_4989_:
{
uint8_t v___x_4995_; uint16_t v___x_4996_; lean_object* v___x_4997_; lean_object* v_env_4998_; uint8_t v___x_4999_; uint16_t v___x_5000_; uint16_t v___x_5001_; uint16_t v___x_5002_; uint8_t v___x_5003_; 
v___x_4995_ = l_Lean_getPPInstantiateMVars(v_opts_4990_);
v___x_4996_ = l_Lean_OptionFlags_ofOptions(v_opts_4990_);
v___x_4997_ = lean_st_ref_get(v___y_4994_);
v_env_4998_ = lean_ctor_get(v___x_4997_, 0);
lean_inc_ref(v_env_4998_);
lean_dec(v___x_4997_);
v___x_4999_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4998_);
lean_dec_ref(v_env_4998_);
v___x_5000_ = 512;
v___x_5001_ = lean_uint16_land(v___x_4996_, v___x_5000_);
v___x_5002_ = 0;
v___x_5003_ = lean_uint16_dec_eq(v___x_5001_, v___x_5002_);
if (v___x_5003_ == 0)
{
if (v___x_4999_ == 0)
{
uint8_t v___x_5004_; 
v___x_5004_ = 1;
v___y_4960_ = v_opts_4990_;
v___y_4961_ = v___y_4992_;
v___y_4962_ = v___y_4993_;
v___y_4963_ = v___y_4994_;
v___y_4964_ = v___x_4996_;
v___y_4965_ = v___x_4995_;
v___y_4966_ = v___x_5004_;
v___y_4967_ = v___y_4991_;
goto v___jp_4959_;
}
else
{
v___y_4931_ = v___y_4992_;
v___y_4932_ = v_opts_4990_;
v___y_4933_ = v___x_4995_;
v___y_4934_ = v___x_4996_;
v___y_4935_ = v___y_4991_;
v___y_4936_ = v___y_4993_;
v___y_4937_ = v___y_4994_;
goto v___jp_4930_;
}
}
else
{
if (v___x_4999_ == 0)
{
v___y_4931_ = v___y_4992_;
v___y_4932_ = v_opts_4990_;
v___y_4933_ = v___x_4995_;
v___y_4934_ = v___x_4996_;
v___y_4935_ = v___y_4991_;
v___y_4936_ = v___y_4993_;
v___y_4937_ = v___y_4994_;
goto v___jp_4930_;
}
else
{
uint8_t v___x_5005_; 
v___x_5005_ = 0;
v___y_4960_ = v_opts_4990_;
v___y_4961_ = v___y_4992_;
v___y_4962_ = v___y_4993_;
v___y_4963_ = v___y_4994_;
v___y_4964_ = v___x_4996_;
v___y_4965_ = v___x_4995_;
v___y_4966_ = v___x_5005_;
v___y_4967_ = v___y_4991_;
goto v___jp_4959_;
}
}
}
v___jp_5006_:
{
if (v___y_5013_ == 0)
{
lean_dec_ref(v___y_5011_);
lean_del_object(v___x_4928_);
v_opts_4990_ = v___y_5008_;
v___y_4991_ = v___y_5007_;
v___y_4992_ = v___y_5012_;
v___y_4993_ = v___y_5009_;
v___y_4994_ = v___y_5010_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5015_; 
lean_dec_ref(v___y_5008_);
lean_dec(v_a_4926_);
lean_dec_ref(v_delab_4818_);
lean_dec(v_optionsPerPos_4817_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set_tag(v___x_4928_, 1);
lean_ctor_set(v___x_4928_, 0, v___y_5011_);
v___x_5015_ = v___x_4928_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___y_5011_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
v___jp_5017_:
{
if (v___y_5024_ == 0)
{
lean_del_object(v___x_4928_);
v_opts_4990_ = v___y_5019_;
v___y_4991_ = v___y_5018_;
v___y_4992_ = v___y_5023_;
v___y_4993_ = v___y_5020_;
v___y_4994_ = v___y_5022_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5025_; 
lean_inc(v_a_4926_);
v___x_5025_ = l_Lean_Meta_isProof(v_a_4926_, v___y_5018_, v___y_5023_, v___y_5020_, v___y_5022_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; uint8_t v___x_5027_; 
lean_del_object(v___x_4928_);
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5025_, 1);
v___x_5027_ = lean_unbox(v_a_5026_);
lean_dec(v_a_5026_);
if (v___x_5027_ == 0)
{
v_opts_4990_ = v___y_5019_;
v___y_4991_ = v___y_5018_;
v___y_4992_ = v___y_5023_;
v___y_4993_ = v___y_5020_;
v___y_4994_ = v___y_5022_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5028_; 
lean_inc_ref(v___y_5021_);
v___x_5028_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(v___y_5019_, v___y_5021_, v___y_5024_);
v_opts_4990_ = v___x_5028_;
v___y_4991_ = v___y_5018_;
v___y_4992_ = v___y_5023_;
v___y_4993_ = v___y_5020_;
v___y_4994_ = v___y_5022_;
goto v___jp_4989_;
}
}
else
{
lean_object* v_a_5029_; uint8_t v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5025_, 1);
v___x_5030_ = l_Lean_Exception_isInterrupt(v_a_5029_);
if (v___x_5030_ == 0)
{
uint8_t v___x_5031_; 
lean_inc(v_a_5029_);
v___x_5031_ = l_Lean_Exception_isRuntime(v_a_5029_);
v___y_5007_ = v___y_5018_;
v___y_5008_ = v___y_5019_;
v___y_5009_ = v___y_5020_;
v___y_5010_ = v___y_5022_;
v___y_5011_ = v_a_5029_;
v___y_5012_ = v___y_5023_;
v___y_5013_ = v___x_5031_;
goto v___jp_5006_;
}
else
{
v___y_5007_ = v___y_5018_;
v___y_5008_ = v___y_5019_;
v___y_5009_ = v___y_5020_;
v___y_5010_ = v___y_5022_;
v___y_5011_ = v_a_5029_;
v___y_5012_ = v___y_5023_;
v___y_5013_ = v___x_5030_;
goto v___jp_5006_;
}
}
}
}
v___jp_5032_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5037_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5035_);
v___x_5038_ = l_Lean_pp_proofs;
v___x_5039_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(v___x_5037_, v___x_5038_);
v___x_5040_ = lean_box(0);
v___x_5041_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(v___x_5039_, v___x_5040_);
lean_dec(v___x_5039_);
if (v___x_5041_ == 0)
{
v___y_5018_ = v___y_5033_;
v___y_5019_ = v___x_5037_;
v___y_5020_ = v___y_5035_;
v___y_5021_ = v___x_5038_;
v___y_5022_ = v___y_5036_;
v___y_5023_ = v___y_5034_;
v___y_5024_ = v___x_5041_;
goto v___jp_5017_;
}
else
{
uint8_t v___x_5042_; 
v___x_5042_ = l_Lean_Expr_isConst(v_a_4926_);
if (v___x_5042_ == 0)
{
v___y_5018_ = v___y_5033_;
v___y_5019_ = v___x_5037_;
v___y_5020_ = v___y_5035_;
v___y_5021_ = v___x_5038_;
v___y_5022_ = v___y_5036_;
v___y_5023_ = v___y_5034_;
v___y_5024_ = v___x_5041_;
goto v___jp_5017_;
}
else
{
lean_del_object(v___x_4928_);
v_opts_4990_ = v___x_5037_;
v___y_4991_ = v___y_5033_;
v___y_4992_ = v___y_5034_;
v___y_4993_ = v___y_5035_;
v___y_4994_ = v___y_5036_;
goto v___jp_4989_;
}
}
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec_ref(v_delab_4818_);
lean_dec(v_optionsPerPos_4817_);
v_a_5063_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_4925_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_4925_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
v___jp_4824_:
{
lean_object* v_infos_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v_infos_4827_ = lean_ctor_get(v_snd_4826_, 1);
lean_inc(v_infos_4827_);
lean_dec_ref(v_snd_4826_);
v___x_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4828_, 0, v_fst_4825_);
lean_ctor_set(v___x_4828_, 1, v_infos_4827_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
v___jp_4830_:
{
if (v___y_4837_ == 0)
{
if (lean_obj_tag(v___y_4832_) == 0)
{
lean_object* v___x_4838_; 
lean_dec_ref(v___y_4831_);
v___x_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___y_4832_);
return v___x_4838_;
}
else
{
lean_object* v_id_4839_; uint8_t v___x_4840_; 
v_id_4839_ = lean_ctor_get(v___y_4832_, 0);
v___x_4840_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4835_, v_id_4839_);
if (v___x_4840_ == 0)
{
lean_object* v___x_4841_; 
lean_dec_ref(v___y_4831_);
v___x_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___y_4832_);
return v___x_4841_;
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref_known(v___y_4832_, 2);
v___x_4842_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4843_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4842_, v___y_4833_, v___y_4836_, v___y_4831_, v___y_4834_);
lean_dec_ref(v___y_4831_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v_fst_4845_; lean_object* v_snd_4846_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___x_4843_, 1);
v_fst_4845_ = lean_ctor_get(v_a_4844_, 0);
lean_inc(v_fst_4845_);
v_snd_4846_ = lean_ctor_get(v_a_4844_, 1);
lean_inc(v_snd_4846_);
lean_dec(v_a_4844_);
v_fst_4825_ = v_fst_4845_;
v_snd_4826_ = v_snd_4846_;
goto v___jp_4824_;
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_a_4847_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4843_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4843_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
}
else
{
lean_object* v___x_4855_; 
lean_dec_ref(v___y_4831_);
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___y_4832_);
return v___x_4855_;
}
}
v___jp_4856_:
{
lean_object* v_toCold_4864_; lean_object* v_currRecDepth_4865_; uint16_t v_optionFlags_4866_; uint8_t v_suppressElabErrors_4867_; uint8_t v_isRecordingDeps_4868_; lean_object* v_currNamespace_4869_; lean_object* v_openDecls_4870_; lean_object* v_lctx_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v_toCold_4864_ = lean_ctor_get(v___y_4862_, 0);
v_currRecDepth_4865_ = lean_ctor_get(v___y_4862_, 1);
v_optionFlags_4866_ = lean_ctor_get_uint16(v___y_4862_, sizeof(void*)*3);
v_suppressElabErrors_4867_ = lean_ctor_get_uint8(v___y_4862_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4868_ = lean_ctor_get_uint8(v___y_4862_, sizeof(void*)*3 + 3);
v_currNamespace_4869_ = lean_ctor_get(v_toCold_4864_, 4);
v_openDecls_4870_ = lean_ctor_get(v_toCold_4864_, 5);
v_lctx_4871_ = lean_ctor_get(v___y_4860_, 2);
v___x_4872_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4873_ = lean_box(0);
v___x_4874_ = l_Lean_Options_getInPattern(v___y_4857_);
lean_dec_ref(v___y_4857_);
v___x_4875_ = l_Lean_SubExpr_mkRoot(v___y_4858_);
v___x_4876_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4871_);
v___x_4877_ = lean_local_ctx_num_indices(v_lctx_4871_);
lean_inc(v_openDecls_4870_);
lean_inc(v_currNamespace_4869_);
v___x_4878_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4878_, 0, v_optionsPerPos_4859_);
lean_ctor_set(v___x_4878_, 1, v_currNamespace_4869_);
lean_ctor_set(v___x_4878_, 2, v_openDecls_4870_);
lean_ctor_set(v___x_4878_, 3, v___x_4875_);
lean_ctor_set(v___x_4878_, 4, v___x_4876_);
lean_ctor_set(v___x_4878_, 5, v___x_4877_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*6, v___x_4874_);
v___x_4879_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4880_ = lean_st_mk_ref(v___x_4879_);
lean_inc(v_currRecDepth_4865_);
lean_inc_ref(v_toCold_4864_);
v___x_4881_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4881_, 0, v_toCold_4864_);
lean_ctor_set(v___x_4881_, 1, v_currRecDepth_4865_);
lean_ctor_set(v___x_4881_, 2, v___x_4873_);
lean_ctor_set_uint16(v___x_4881_, sizeof(void*)*3, v_optionFlags_4866_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*3 + 2, v_suppressElabErrors_4867_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*3 + 3, v_isRecordingDeps_4868_);
lean_inc(v___y_4863_);
lean_inc(v___y_4861_);
lean_inc_ref(v___y_4860_);
lean_inc(v___x_4880_);
v___x_4882_ = lean_apply_7(v_delab_4818_, v___x_4878_, v___x_4880_, v___y_4860_, v___y_4861_, v___x_4881_, v___y_4863_, lean_box(0));
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; 
lean_dec_ref(v___y_4862_);
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v___x_4882_, 1);
v___x_4884_ = lean_st_ref_get(v___x_4880_);
lean_dec(v___x_4880_);
v_fst_4825_ = v_a_4883_;
v_snd_4826_ = v___x_4884_;
goto v___jp_4824_;
}
else
{
lean_object* v_a_4885_; uint8_t v___x_4886_; 
lean_dec(v___x_4880_);
v_a_4885_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4882_, 1);
v___x_4886_ = l_Lean_Exception_isInterrupt(v_a_4885_);
if (v___x_4886_ == 0)
{
uint8_t v___x_4887_; 
lean_inc(v_a_4885_);
v___x_4887_ = l_Lean_Exception_isRuntime(v_a_4885_);
v___y_4831_ = v___y_4862_;
v___y_4832_ = v_a_4885_;
v___y_4833_ = v___y_4860_;
v___y_4834_ = v___y_4863_;
v___y_4835_ = v___x_4872_;
v___y_4836_ = v___y_4861_;
v___y_4837_ = v___x_4887_;
goto v___jp_4830_;
}
else
{
v___y_4831_ = v___y_4862_;
v___y_4832_ = v_a_4885_;
v___y_4833_ = v___y_4860_;
v___y_4834_ = v___y_4863_;
v___y_4835_ = v___x_4872_;
v___y_4836_ = v___y_4861_;
v___y_4837_ = v___x_4886_;
goto v___jp_4830_;
}
}
}
v___jp_4888_:
{
uint8_t v___x_4895_; 
v___x_4895_ = l_Lean_getPPAll(v___y_4889_);
if (v___x_4895_ == 0)
{
uint8_t v___x_4896_; 
v___x_4896_ = l_Lean_getPPAnalyze(v___y_4889_);
if (v___x_4896_ == 0)
{
v___y_4857_ = v___y_4889_;
v___y_4858_ = v_e_4890_;
v_optionsPerPos_4859_ = v_optionsPerPos_4817_;
v___y_4860_ = v___y_4891_;
v___y_4861_ = v___y_4892_;
v___y_4862_ = v___y_4893_;
v___y_4863_ = v___y_4894_;
goto v___jp_4856_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4817_) == 0)
{
v___y_4857_ = v___y_4889_;
v___y_4858_ = v_e_4890_;
v_optionsPerPos_4859_ = v_optionsPerPos_4817_;
v___y_4860_ = v___y_4891_;
v___y_4861_ = v___y_4892_;
v___y_4862_ = v___y_4893_;
v___y_4863_ = v___y_4894_;
goto v___jp_4856_;
}
else
{
lean_object* v___x_4897_; 
lean_inc_ref(v_e_4890_);
v___x_4897_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref_known(v___x_4897_, 1);
v___y_4857_ = v___y_4889_;
v___y_4858_ = v_e_4890_;
v_optionsPerPos_4859_ = v_a_4898_;
v___y_4860_ = v___y_4891_;
v___y_4861_ = v___y_4892_;
v___y_4862_ = v___y_4893_;
v___y_4863_ = v___y_4894_;
goto v___jp_4856_;
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_dec_ref(v___y_4893_);
lean_dec_ref(v_e_4890_);
lean_dec_ref(v___y_4889_);
lean_dec_ref(v_delab_4818_);
v_a_4899_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4897_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4897_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
}
else
{
v___y_4857_ = v___y_4889_;
v___y_4858_ = v_e_4890_;
v_optionsPerPos_4859_ = v_optionsPerPos_4817_;
v___y_4860_ = v___y_4891_;
v___y_4861_ = v___y_4892_;
v___y_4862_ = v___y_4893_;
v___y_4863_ = v___y_4894_;
goto v___jp_4856_;
}
}
v___jp_4907_:
{
uint8_t v___x_4914_; 
v___x_4914_ = l_Lean_getPPBeta(v___y_4908_);
if (v___x_4914_ == 0)
{
v___y_4889_ = v___y_4908_;
v_e_4890_ = v_e_4909_;
v___y_4891_ = v___y_4910_;
v___y_4892_ = v___y_4911_;
v___y_4893_ = v___y_4912_;
v___y_4894_ = v___y_4913_;
goto v___jp_4888_;
}
else
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Lean_Core_betaReduce(v_e_4909_, v___y_4912_, v___y_4913_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___y_4889_ = v___y_4908_;
v_e_4890_ = v_a_4916_;
v___y_4891_ = v___y_4910_;
v___y_4892_ = v___y_4911_;
v___y_4893_ = v___y_4912_;
v___y_4894_ = v___y_4913_;
goto v___jp_4888_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec_ref(v___y_4912_);
lean_dec_ref(v___y_4908_);
lean_dec_ref(v_delab_4818_);
lean_dec(v_optionsPerPos_4817_);
v_a_4917_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4915_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4915_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5071_, lean_object* v_optionsPerPos_5072_, lean_object* v_delab_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5071_, v_optionsPerPos_5072_, v_delab_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5080_, lean_object* v_e_5081_, lean_object* v_optionsPerPos_5082_, lean_object* v_delab_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5081_, v_optionsPerPos_5082_, v_delab_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5090_, lean_object* v_e_5091_, lean_object* v_optionsPerPos_5092_, lean_object* v_delab_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5090_, v_e_5091_, v_optionsPerPos_5092_, v_delab_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5101_, lean_object* v_optionsPerPos_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5108_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5109_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5101_, v_optionsPerPos_5102_, v___x_5108_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5118_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5112_ = v___x_5109_;
v_isShared_5113_ = v_isSharedCheck_5118_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5109_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5118_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_fst_5114_; lean_object* v___x_5116_; 
v_fst_5114_ = lean_ctor_get(v_a_5110_, 0);
lean_inc(v_fst_5114_);
lean_dec(v_a_5110_);
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 0, v_fst_5114_);
v___x_5116_ = v___x_5112_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_fst_5114_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
v_a_5119_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5109_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5109_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5127_, lean_object* v_optionsPerPos_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_PrettyPrinter_delab(v_e_5127_, v_optionsPerPos_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5199_; uint8_t v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5199_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5200_ = 0;
v___x_5201_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5202_ = l_Lean_registerTraceClass(v___x_5199_, v___x_5200_, v___x_5201_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v___x_5203_; lean_object* v___x_5204_; 
lean_dec_ref_known(v___x_5202_, 1);
v___x_5203_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5204_ = l_Lean_registerTraceClass(v___x_5203_, v___x_5200_, v___x_5201_);
return v___x_5204_;
}
else
{
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5206_;
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
