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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPProofsThreshold___boxed(lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_maxChildren;
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPDeepTermsThreshold___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPProofsWithType___boxed(lean_object*);
uint8_t l_Lean_Options_getInPattern(lean_object*);
lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_getPPAll(lean_object*);
uint8_t l_Lean_getPPAnalyze(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPBeta(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPAnalyzeTypeAscriptions___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPAnalysisNeedsType___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__7_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__8 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__8_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_delab___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__10;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value),LEAN_SCALAR_PTR_LITERAL(231, 152, 1, 212, 81, 225, 23, 202)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__17 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__18 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__19 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__20 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__21 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__22 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__22_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__22_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__23 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__23_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__23_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__24 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__24_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__25 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__25_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__0;
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__1;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.PrettyPrinter.Delaborator.Basic"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PrettyPrinter.delabCore"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__3_value;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__4_value;
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
lean_object* v_a_50_; uint8_t v___x_51_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v___x_51_ = l_Lean_Exception_isInterrupt(v_a_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
lean_inc(v_a_50_);
v___x_52_ = l_Lean_Exception_isRuntime(v_a_50_);
if (v___x_52_ == 0)
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
else
{
lean_dec(v_a_50_);
lean_dec_ref(v_d_u2082_40_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg___boxed(lean_object* v_d_u2081_57_, lean_object* v_d_u2082_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_PrettyPrinter_Delaborator_orElse___redArg(v_d_u2081_57_, v_d_u2082_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object* v_00_u03b1_67_, lean_object* v_d_u2081_68_, lean_object* v_d_u2082_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
v___x_78_ = lean_apply_7(v_d_u2081_68_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, lean_box(0));
if (lean_obj_tag(v___x_78_) == 0)
{
lean_dec_ref(v_d_u2082_69_);
return v___x_78_;
}
else
{
lean_object* v_a_79_; uint8_t v___x_80_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
v___x_80_ = l_Lean_Exception_isInterrupt(v_a_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
lean_inc(v_a_79_);
v___x_81_ = l_Lean_Exception_isRuntime(v_a_79_);
if (v___x_81_ == 0)
{
if (lean_obj_tag(v_a_79_) == 0)
{
lean_dec_ref_known(v_a_79_, 2);
lean_dec_ref(v_d_u2082_69_);
return v___x_78_;
}
else
{
lean_object* v_id_82_; uint8_t v___x_83_; 
v_id_82_ = lean_ctor_get(v_a_79_, 0);
lean_inc(v_id_82_);
lean_dec_ref_known(v_a_79_, 2);
v___x_83_ = l_Lean_instBEqInternalExceptionId_beq(v___x_77_, v_id_82_);
lean_dec(v_id_82_);
if (v___x_83_ == 0)
{
lean_dec_ref(v_d_u2082_69_);
return v___x_78_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec_ref_known(v___x_78_, 1);
v___x_84_ = lean_box(0);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
v___x_85_ = lean_apply_8(v_d_u2082_69_, v___x_84_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, lean_box(0));
return v___x_85_;
}
}
}
else
{
lean_dec(v_a_79_);
lean_dec_ref(v_d_u2082_69_);
return v___x_78_;
}
}
else
{
lean_dec(v_a_79_);
lean_dec_ref(v_d_u2082_69_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___boxed(lean_object* v_00_u03b1_86_, lean_object* v_d_u2081_87_, lean_object* v_d_u2082_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_PrettyPrinter_Delaborator_orElse(v_00_u03b1_86_, v_d_u2081_87_, v_d_u2082_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_96_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_box(0);
v___x_98_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg(){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0, &l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg___boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object* v_00_u03b1_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object* v_00_u03b1_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_PrettyPrinter_Delaborator_failure(v_00_u03b1_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_instMonadEIO___redArg();
return v___x_123_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0);
v___x_125_ = l_StateRefT_x27_instMonad___redArg(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM(void){
_start:
{
lean_object* v___x_132_; lean_object* v_toApplicative_133_; lean_object* v_toFunctor_134_; lean_object* v_toSeq_135_; lean_object* v_toSeqLeft_136_; lean_object* v_toSeqRight_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_toApplicative_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_200_; 
v___x_132_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
v_toApplicative_133_ = lean_ctor_get(v___x_132_, 0);
v_toFunctor_134_ = lean_ctor_get(v_toApplicative_133_, 0);
v_toSeq_135_ = lean_ctor_get(v_toApplicative_133_, 2);
v_toSeqLeft_136_ = lean_ctor_get(v_toApplicative_133_, 3);
v_toSeqRight_137_ = lean_ctor_get(v_toApplicative_133_, 4);
v___f_138_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2));
v___f_139_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3));
lean_inc_ref_n(v_toFunctor_134_, 2);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_134_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_141_, 0, v_toFunctor_134_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___f_140_);
lean_ctor_set(v___x_142_, 1, v___f_141_);
lean_inc(v_toSeqRight_137_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqRight_137_);
lean_inc(v_toSeqLeft_136_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeqLeft_136_);
lean_inc(v_toSeq_135_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeq_135_);
v___x_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___f_138_);
lean_ctor_set(v___x_146_, 2, v___f_145_);
lean_ctor_set(v___x_146_, 3, v___f_144_);
lean_ctor_set(v___x_146_, 4, v___f_143_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___f_139_);
v___x_148_ = l_StateRefT_x27_instMonad___redArg(v___x_147_);
v_toApplicative_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v___x_148_, 1);
lean_dec(v_unused_201_);
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_200_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_toApplicative_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_200_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_toFunctor_153_; lean_object* v_toSeq_154_; lean_object* v_toSeqLeft_155_; lean_object* v_toSeqRight_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_198_; 
v_toFunctor_153_ = lean_ctor_get(v_toApplicative_149_, 0);
v_toSeq_154_ = lean_ctor_get(v_toApplicative_149_, 2);
v_toSeqLeft_155_ = lean_ctor_get(v_toApplicative_149_, 3);
v_toSeqRight_156_ = lean_ctor_get(v_toApplicative_149_, 4);
v_isSharedCheck_198_ = !lean_is_exclusive(v_toApplicative_149_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_dec(v_unused_199_);
v___x_158_ = v_toApplicative_149_;
v_isShared_159_ = v_isSharedCheck_198_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_toSeqRight_156_);
lean_inc(v_toSeqLeft_155_);
lean_inc(v_toSeq_154_);
lean_inc(v_toFunctor_153_);
lean_dec(v_toApplicative_149_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_198_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_169_; 
v___f_160_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4));
v___f_161_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5));
lean_inc_ref(v_toFunctor_153_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_162_, 0, v_toFunctor_153_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_163_, 0, v_toFunctor_153_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___f_162_);
lean_ctor_set(v___x_164_, 1, v___f_163_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_165_, 0, v_toSeqRight_156_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeqLeft_155_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeq_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 4, v___f_165_);
lean_ctor_set(v___x_158_, 3, v___f_166_);
lean_ctor_set(v___x_158_, 2, v___f_167_);
lean_ctor_set(v___x_158_, 1, v___f_160_);
lean_ctor_set(v___x_158_, 0, v___x_164_);
v___x_169_ = v___x_158_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___f_160_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v___f_166_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v___f_165_);
v___x_169_ = v_reuseFailAlloc_197_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___f_161_);
lean_ctor_set(v___x_151_, 0, v___x_169_);
v___x_171_ = v___x_151_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___f_161_);
v___x_171_ = v_reuseFailAlloc_196_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v_toApplicative_173_; lean_object* v_toFunctor_174_; lean_object* v_toSeq_175_; lean_object* v_toSeqLeft_176_; lean_object* v_toSeqRight_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_194_; 
v___x_172_ = l_StateRefT_x27_instMonad___redArg(v___x_171_);
v_toApplicative_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc_ref(v_toApplicative_173_);
v_toFunctor_174_ = lean_ctor_get(v_toApplicative_173_, 0);
v_toSeq_175_ = lean_ctor_get(v_toApplicative_173_, 2);
v_toSeqLeft_176_ = lean_ctor_get(v_toApplicative_173_, 3);
v_toSeqRight_177_ = lean_ctor_get(v_toApplicative_173_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v_toApplicative_173_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_toApplicative_173_, 1);
lean_dec(v_unused_195_);
v___x_179_ = v_toApplicative_173_;
v_isShared_180_ = v_isSharedCheck_194_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_toSeqRight_177_);
lean_inc(v_toSeqLeft_176_);
lean_inc(v_toSeq_175_);
lean_inc(v_toFunctor_174_);
lean_dec(v_toApplicative_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_194_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqRight_177_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeqLeft_176_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_183_, 0, v_toSeq_175_);
lean_inc_ref(v_toFunctor_174_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_184_, 0, v_toFunctor_174_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_185_, 0, v_toFunctor_174_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___f_184_);
lean_ctor_set(v___x_186_, 1, v___f_185_);
v___x_187_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_187_, 0, lean_box(0));
lean_closure_set(v___x_187_, 1, lean_box(0));
lean_closure_set(v___x_187_, 2, v___x_172_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 4, v___f_181_);
lean_ctor_set(v___x_179_, 3, v___f_182_);
lean_ctor_set(v___x_179_, 2, v___f_183_);
lean_ctor_set(v___x_179_, 1, v___x_187_);
lean_ctor_set(v___x_179_, 0, v___x_186_);
v___x_189_ = v___x_179_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___f_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v___f_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v___f_181_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6));
v___x_191_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7));
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_189_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_191_);
return v___x_192_;
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
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___boxed(lean_object* v___dummy_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg();
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* v_00_u03b1_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___redArg___closed__0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_subExpr_216_; lean_object* v___x_217_; 
v_subExpr_216_ = lean_ctor_get(v___y_209_, 3);
lean_inc_ref(v_subExpr_216_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v_subExpr_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed(lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(lean_object* v_00_u03b1_228_, lean_object* v_f_229_, lean_object* v_x_230_, lean_object* v_ctx_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_optionsPerPos_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; uint8_t v_inPattern_241_; lean_object* v_subExpr_242_; lean_object* v_depth_243_; lean_object* v_lctxInitIndices_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_253_; 
v_optionsPerPos_238_ = lean_ctor_get(v_ctx_231_, 0);
v_currNamespace_239_ = lean_ctor_get(v_ctx_231_, 1);
v_openDecls_240_ = lean_ctor_get(v_ctx_231_, 2);
v_inPattern_241_ = lean_ctor_get_uint8(v_ctx_231_, sizeof(void*)*6);
v_subExpr_242_ = lean_ctor_get(v_ctx_231_, 3);
v_depth_243_ = lean_ctor_get(v_ctx_231_, 4);
v_lctxInitIndices_244_ = lean_ctor_get(v_ctx_231_, 5);
v_isSharedCheck_253_ = !lean_is_exclusive(v_ctx_231_);
if (v_isSharedCheck_253_ == 0)
{
v___x_246_ = v_ctx_231_;
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_lctxInitIndices_244_);
lean_inc(v_depth_243_);
lean_inc(v_subExpr_242_);
lean_inc(v_openDecls_240_);
lean_inc(v_currNamespace_239_);
lean_inc(v_optionsPerPos_238_);
lean_dec(v_ctx_231_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_253_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_apply_1(v_f_229_, v_subExpr_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 3, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_optionsPerPos_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_currNamespace_239_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_openDecls_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_depth_243_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_lctxInitIndices_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*6, v_inPattern_241_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; 
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
v___x_251_ = lean_apply_7(v_x_230_, v___x_250_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, lean_box(0));
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object* v_00_u03b1_254_, lean_object* v_f_255_, lean_object* v_x_256_, lean_object* v_ctx_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(v_00_u03b1_254_, v_f_255_, v_x_256_, v_ctx_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_holeIter_275_; lean_object* v___x_276_; 
v___x_274_ = lean_st_ref_get(v___y_268_);
v_holeIter_275_ = lean_ctor_get(v___x_274_, 2);
lean_inc_ref(v_holeIter_275_);
lean_dec(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_holeIter_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object* v_iter_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; lean_object* v_steps_294_; lean_object* v_infos_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v___x_293_ = lean_st_ref_take(v___y_287_);
v_steps_294_ = lean_ctor_get(v___x_293_, 0);
v_infos_295_ = lean_ctor_get(v___x_293_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_293_, 2);
lean_dec(v_unused_306_);
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_infos_295_);
lean_inc(v_steps_294_);
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v_iter_285_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_steps_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_infos_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_iter_285_);
v___x_301_ = v_reuseFailAlloc_304_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_st_ref_put(v___y_287_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_299_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object* v_iter_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(v_iter_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object* v_00_u03b1_316_, lean_object* v_f_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_steps_326_; lean_object* v_infos_327_; lean_object* v_holeIter_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_340_; 
v___x_325_ = lean_st_ref_take(v___y_319_);
v_steps_326_ = lean_ctor_get(v___x_325_, 0);
v_infos_327_ = lean_ctor_get(v___x_325_, 1);
v_holeIter_328_ = lean_ctor_get(v___x_325_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_340_ == 0)
{
v___x_330_ = v___x_325_;
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_holeIter_328_);
lean_inc(v_infos_327_);
lean_inc(v_steps_326_);
lean_dec(v___x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_336_; 
v___x_332_ = lean_apply_1(v_f_317_, v_holeIter_328_);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_snd_334_);
lean_dec_ref(v___x_332_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 2, v_snd_334_);
v___x_336_ = v___x_330_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_steps_326_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_infos_327_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_snd_334_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_st_ref_put(v___y_319_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_fst_333_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object* v_00_u03b1_341_, lean_object* v_f_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(v_00_u03b1_341_, v_f_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_builtin_359_, lean_object* v_declName_360_, lean_object* v_key_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_builtin_367_, lean_object* v_declName_368_, lean_object* v_key_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_builtin_boxed_373_; lean_object* v_res_374_; 
v_builtin_boxed_373_ = lean_unbox(v_builtin_367_);
v_res_374_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_builtin_boxed_373_, v_declName_368_, v_key_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v_key_369_);
lean_dec(v_declName_368_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_375_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_379_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_ctor_set(v___x_381_, 3, v___x_380_);
lean_ctor_set(v___x_381_, 4, v___x_379_);
lean_ctor_set(v___x_381_, 5, v___x_379_);
lean_ctor_set(v___x_381_, 6, v___x_379_);
lean_ctor_set(v___x_381_, 7, v___x_379_);
lean_ctor_set(v___x_381_, 8, v___x_379_);
lean_ctor_set(v___x_381_, 9, v___x_379_);
lean_ctor_set(v___x_381_, 10, v___x_379_);
lean_ctor_set(v___x_381_, 11, v___x_378_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_unsigned_to_nat(32u);
v___x_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = ((size_t)5ULL);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_unsigned_to_nat(32u);
v___x_388_ = lean_mk_empty_array_with_capacity(v___x_387_);
v___x_389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_390_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_386_);
lean_ctor_set(v___x_390_, 3, v___x_386_);
lean_ctor_set_usize(v___x_390_, 4, v___x_385_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_box(1);
v___x_392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_416_, lean_object* v_declHint_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_env_422_; uint8_t v___x_423_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_st_ref_get(v___y_418_);
v_env_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_422_);
lean_dec(v___x_421_);
v___x_423_ = l_Lean_Name_isAnonymous(v_declHint_417_);
if (v___x_423_ == 0)
{
uint8_t v_isExporting_424_; 
v_isExporting_424_ = lean_ctor_get_uint8(v_env_422_, sizeof(void*)*13);
if (v_isExporting_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec_ref(v_env_422_);
lean_dec(v_declHint_417_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_msg_416_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; uint8_t v___x_427_; 
lean_inc_ref(v_env_422_);
v___x_426_ = l_Lean_Environment_setExporting(v_env_422_, v___x_423_);
lean_inc(v_declHint_417_);
lean_inc_ref(v___x_426_);
v___x_427_ = l_Lean_Environment_contains(v___x_426_, v_declHint_417_, v_isExporting_424_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v___x_426_);
lean_dec_ref(v_env_422_);
lean_dec(v_declHint_417_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_msg_416_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_c_434_; lean_object* v___x_435_; 
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_430_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_431_ = l_Lean_Options_empty;
v___x_432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_426_);
lean_ctor_set(v___x_432_, 1, v___x_429_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_inc(v_declHint_417_);
v___x_433_ = l_Lean_MessageData_ofConstName(v_declHint_417_, v___x_423_);
v_c_434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_434_, 0, v___x_432_);
lean_ctor_set(v_c_434_, 1, v___x_433_);
v___x_435_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_422_, v_declHint_417_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_env_422_);
lean_dec(v_declHint_417_);
v___x_436_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_c_434_);
v___x_438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_MessageData_note(v___x_439_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v_msg_416_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_477_; 
v_val_443_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_477_ == 0)
{
v___x_445_ = v___x_435_;
v_isShared_446_ = v_isSharedCheck_477_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v___x_435_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_477_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v_moduleNames_448_; lean_object* v_mod_449_; uint8_t v___x_450_; 
v___x_447_ = l_Lean_Environment_header(v_env_422_);
lean_dec_ref(v_env_422_);
v_moduleNames_448_ = lean_ctor_get(v___x_447_, 4);
lean_inc_ref(v_moduleNames_448_);
lean_dec_ref(v___x_447_);
v_mod_449_ = lean_array_get(v___x_420_, v_moduleNames_448_, v_val_443_);
lean_dec(v_val_443_);
lean_dec_ref(v_moduleNames_448_);
v___x_450_ = l_Lean_isPrivateName(v_declHint_417_);
lean_dec(v_declHint_417_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_c_434_);
v___x_453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_MessageData_ofName(v_mod_449_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_MessageData_note(v___x_458_);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v_msg_416_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 0);
lean_ctor_set(v___x_445_, 0, v___x_460_);
v___x_462_ = v___x_445_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_c_434_);
v___x_466_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_MessageData_ofName(v_mod_449_);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Lean_MessageData_note(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v_msg_416_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 0);
lean_ctor_set(v___x_445_, 0, v___x_473_);
v___x_475_ = v___x_445_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v_env_422_);
lean_dec(v_declHint_417_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_msg_416_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_479_, lean_object* v_declHint_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_479_, v_declHint_480_, v___y_481_);
lean_dec(v___y_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object* v_msg_484_, lean_object* v_declHint_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v___x_489_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_484_, v_declHint_485_, v___y_487_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_499_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = l_Lean_unknownIdentifierMessageTag;
v___x_495_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_500_, lean_object* v_declHint_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_500_, v_declHint_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; lean_object* v_toCold_511_; lean_object* v_env_512_; lean_object* v_options_513_; uint8_t v___x_514_; lean_object* v_env_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_510_ = lean_st_ref_get(v___y_508_);
v_toCold_511_ = lean_ctor_get(v___y_507_, 0);
v_env_512_ = lean_ctor_get(v___x_510_, 0);
lean_inc_ref(v_env_512_);
lean_dec(v___x_510_);
v_options_513_ = lean_ctor_get(v_toCold_511_, 2);
v___x_514_ = 0;
v_env_515_ = l_Lean_Environment_setRecordingDeps(v_env_512_, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_517_ = lean_unsigned_to_nat(32u);
v___x_518_ = lean_mk_empty_array_with_capacity(v___x_517_);
lean_dec_ref(v___x_518_);
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_513_);
v___x_520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_520_, 0, v_env_515_);
lean_ctor_set(v___x_520_, 1, v___x_516_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
lean_ctor_set(v___x_520_, 3, v_options_513_);
v___x_521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v_msgData_506_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msgData_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_ref_532_; lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_ref_532_ = lean_ctor_get(v___y_529_, 2);
v___x_533_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_528_, v___y_529_, v___y_530_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_inc(v_ref_532_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_ref_532_);
lean_ctor_set(v___x_538_, 1, v_a_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 1);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_toCold_553_; lean_object* v_currRecDepth_554_; lean_object* v_ref_555_; uint16_t v_optionFlags_556_; uint8_t v_suppressElabErrors_557_; uint8_t v_isRecordingDeps_558_; lean_object* v_ref_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_toCold_553_ = lean_ctor_get(v___y_550_, 0);
v_currRecDepth_554_ = lean_ctor_get(v___y_550_, 1);
v_ref_555_ = lean_ctor_get(v___y_550_, 2);
v_optionFlags_556_ = lean_ctor_get_uint16(v___y_550_, sizeof(void*)*3);
v_suppressElabErrors_557_ = lean_ctor_get_uint8(v___y_550_, sizeof(void*)*3 + 2);
v_isRecordingDeps_558_ = lean_ctor_get_uint8(v___y_550_, sizeof(void*)*3 + 3);
v_ref_559_ = l_Lean_replaceRef(v_ref_548_, v_ref_555_);
lean_inc(v_currRecDepth_554_);
lean_inc_ref(v_toCold_553_);
v___x_560_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_560_, 0, v_toCold_553_);
lean_ctor_set(v___x_560_, 1, v_currRecDepth_554_);
lean_ctor_set(v___x_560_, 2, v_ref_559_);
lean_ctor_set_uint16(v___x_560_, sizeof(void*)*3, v_optionFlags_556_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 2, v_suppressElabErrors_557_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 3, v_isRecordingDeps_558_);
v___x_561_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_549_, v___x_560_, v___y_551_);
lean_dec_ref_known(v___x_560_, 3);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_562_, v_msg_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_ref_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_569_, v_declHint_570_, v___y_571_, v___y_572_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_568_, v_a_575_, v___y_571_, v___y_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_577_, lean_object* v_msg_578_, lean_object* v_declHint_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_577_, v_msg_578_, v_declHint_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_ref_577_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object* v_ref_590_, lean_object* v_constName_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1);
v___x_596_ = 0;
lean_inc(v_constName_591_);
v___x_597_ = l_Lean_MessageData_ofConstName(v_constName_591_, v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_590_, v___x_600_, v_constName_591_, v___y_592_, v___y_593_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_ref_602_, lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_602_, v_constName_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v_ref_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object* v_constName_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_ref_612_; lean_object* v___x_613_; 
v_ref_612_ = lean_ctor_get(v___y_609_, 2);
v___x_613_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_612_, v_constName_608_, v___y_609_, v___y_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_constName_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_constName_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_env_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_st_ref_get(v___y_621_);
v_env_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_env_624_);
lean_dec(v___x_623_);
v___x_625_ = 0;
lean_inc(v_constName_619_);
v___x_626_ = l_Lean_Environment_findConstVal_x3f(v_env_624_, v_constName_619_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_619_, v___y_620_, v___y_621_);
return v___x_627_;
}
else
{
lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_constName_619_);
v_val_628_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_626_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_dec(v___x_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 0);
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_val_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_constName_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_List_reverse___redArg(v_a_642_);
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_654_; 
v_head_644_ = lean_ctor_get(v_a_641_, 0);
v_tail_645_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_647_ = v_a_641_;
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_tail_645_);
lean_inc(v_head_644_);
lean_dec(v_a_641_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l_Lean_mkLevelParam(v_head_644_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_a_642_);
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_642_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_641_ = v_tail_645_;
v_a_642_ = v___x_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v_constName_655_);
v___x_659_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_671_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_levelParams_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v_levelParams_664_ = lean_ctor_get(v_a_660_, 1);
lean_inc(v_levelParams_664_);
lean_dec(v_a_660_);
v___x_665_ = lean_box(0);
v___x_666_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_levelParams_664_, v___x_665_);
v___x_667_ = l_Lean_mkConst(v_constName_655_, v___x_666_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_667_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v_constName_655_);
v_a_672_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_659_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_659_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_constName_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_constName_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_t_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_infoState_689_; uint8_t v_enabled_690_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_infoState_689_ = lean_ctor_get(v___x_688_, 8);
lean_inc_ref(v_infoState_689_);
lean_dec(v___x_688_);
v_enabled_690_ = lean_ctor_get_uint8(v_infoState_689_, sizeof(void*)*3);
lean_dec_ref(v_infoState_689_);
if (v_enabled_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v_t_685_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v_infoState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_traceState_699_; lean_object* v_cache_700_; lean_object* v_recordedDeps_701_; lean_object* v_messages_702_; lean_object* v_snapshotTasks_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_725_; 
v___x_693_ = lean_st_ref_take(v___y_686_);
v_infoState_694_ = lean_ctor_get(v___x_693_, 8);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_traceState_699_ = lean_ctor_get(v___x_693_, 4);
v_cache_700_ = lean_ctor_get(v___x_693_, 5);
v_recordedDeps_701_ = lean_ctor_get(v___x_693_, 6);
v_messages_702_ = lean_ctor_get(v___x_693_, 7);
v_snapshotTasks_703_ = lean_ctor_get(v___x_693_, 9);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_725_ == 0)
{
v___x_705_ = v___x_693_;
v_isShared_706_ = v_isSharedCheck_725_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snapshotTasks_703_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_702_);
lean_inc(v_recordedDeps_701_);
lean_inc(v_cache_700_);
lean_inc(v_traceState_699_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_725_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v_enabled_707_; lean_object* v_assignment_708_; lean_object* v_lazyAssignment_709_; lean_object* v_trees_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_724_; 
v_enabled_707_ = lean_ctor_get_uint8(v_infoState_694_, sizeof(void*)*3);
v_assignment_708_ = lean_ctor_get(v_infoState_694_, 0);
v_lazyAssignment_709_ = lean_ctor_get(v_infoState_694_, 1);
v_trees_710_ = lean_ctor_get(v_infoState_694_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_infoState_694_);
if (v_isSharedCheck_724_ == 0)
{
v___x_712_ = v_infoState_694_;
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_trees_710_);
lean_inc(v_lazyAssignment_709_);
lean_inc(v_assignment_708_);
lean_dec(v_infoState_694_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_box(0);
v___x_715_ = l_Lean_PersistentArray_push___redArg(v_trees_710_, v_t_685_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 2, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_assignment_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_lazyAssignment_709_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v___x_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_723_, sizeof(void*)*3, v_enabled_707_);
v___x_717_ = v_reuseFailAlloc_723_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 8, v___x_717_);
v___x_719_ = v___x_705_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_traceState_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_cache_700_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_recordedDeps_701_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_messages_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_snapshotTasks_703_);
v___x_719_ = v_reuseFailAlloc_722_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_st_ref_put(v___y_686_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_714_);
return v___x_721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_726_, v___y_727_);
lean_dec(v___y_727_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
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
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_733_ = ((size_t)5ULL);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_unsigned_to_nat(32u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
v___x_737_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_738_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v___x_734_);
lean_ctor_set(v___x_738_, 3, v___x_734_);
lean_ctor_set_usize(v___x_738_, 4, v___x_733_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_t_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_infoState_744_; uint8_t v_enabled_745_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_infoState_744_ = lean_ctor_get(v___x_743_, 8);
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
v___x_748_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v_t_739_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_749_, v___y_741_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_t_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v_t_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(lean_object* v_stx_756_, lean_object* v_n_757_, lean_object* v_expectedType_x3f_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_n_757_, v___y_759_, v___y_760_);
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
v___x_770_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_769_, v___y_759_, v___y_760_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_779_, lean_object* v_n_780_, lean_object* v_expectedType_x3f_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v_stx_779_, v_n_780_, v_expectedType_x3f_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(lean_object* v_info_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_790_, 0, v_info_786_);
v___x_791_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_790_, v___y_787_, v___y_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0___boxed(lean_object* v_info_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v_info_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object* v_a_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
else
{
lean_object* v_key_800_; lean_object* v_value_801_; lean_object* v_tail_802_; uint8_t v___x_803_; 
v_key_800_ = lean_ctor_get(v_x_798_, 0);
v_value_801_ = lean_ctor_get(v_x_798_, 1);
v_tail_802_ = lean_ctor_get(v_x_798_, 2);
v___x_803_ = lean_name_eq(v_key_800_, v_a_797_);
if (v___x_803_ == 0)
{
v_x_798_ = v_tail_802_;
goto _start;
}
else
{
lean_object* v___x_805_; 
lean_inc(v_value_801_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_value_801_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec(v_a_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_buckets_811_; lean_object* v___x_812_; uint64_t v___y_814_; 
v_buckets_811_ = lean_ctor_get(v_m_809_, 1);
v___x_812_ = lean_array_get_size(v_buckets_811_);
if (lean_obj_tag(v_a_810_) == 0)
{
uint64_t v___x_828_; 
v___x_828_ = 1723ULL;
v___y_814_ = v___x_828_;
goto v___jp_813_;
}
else
{
uint64_t v_hash_829_; 
v_hash_829_ = lean_ctor_get_uint64(v_a_810_, sizeof(void*)*2);
v___y_814_ = v_hash_829_;
goto v___jp_813_;
}
v___jp_813_:
{
uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v_fold_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_815_ = 32ULL;
v___x_816_ = lean_uint64_shift_right(v___y_814_, v___x_815_);
v_fold_817_ = lean_uint64_xor(v___y_814_, v___x_816_);
v___x_818_ = 16ULL;
v___x_819_ = lean_uint64_shift_right(v_fold_817_, v___x_818_);
v___x_820_ = lean_uint64_xor(v_fold_817_, v___x_819_);
v___x_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = lean_usize_of_nat(v___x_812_);
v___x_823_ = ((size_t)1ULL);
v___x_824_ = lean_usize_sub(v___x_822_, v___x_823_);
v___x_825_ = lean_usize_land(v___x_821_, v___x_824_);
v___x_826_ = lean_array_uget_borrowed(v_buckets_811_, v___x_825_);
v___x_827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_810_, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_m_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_m_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___lam__0(lean_object* v___x_833_, lean_object* v_entry_834_, lean_object* v_s_835_){
_start:
{
lean_object* v_addEntryFn_836_; lean_object* v_importedEntries_837_; lean_object* v_state_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_addEntryFn_836_ = lean_ctor_get(v___x_833_, 3);
lean_inc(v_addEntryFn_836_);
lean_dec_ref(v___x_833_);
v_importedEntries_837_ = lean_ctor_get(v_s_835_, 0);
v_state_838_ = lean_ctor_get(v_s_835_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_s_835_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v_s_835_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_state_838_);
lean_inc(v_importedEntries_837_);
lean_dec(v_s_835_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_state_842_; lean_object* v___x_844_; 
v_state_842_ = lean_apply_2(v_addEntryFn_836_, v_state_838_, v_entry_834_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_state_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_importedEntries_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_state_842_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_keys_847_, lean_object* v_i_848_, lean_object* v_k_849_){
_start:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_array_get_size(v_keys_847_);
v___x_851_ = lean_nat_dec_lt(v_i_848_, v___x_850_);
if (v___x_851_ == 0)
{
lean_dec(v_i_848_);
return v___x_851_;
}
else
{
lean_object* v_k_x27_852_; uint8_t v___x_853_; 
v_k_x27_852_ = lean_array_fget_borrowed(v_keys_847_, v_i_848_);
v___x_853_ = l_Lean_instBEqExtraModUse_beq(v_k_849_, v_k_x27_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_add(v_i_848_, v___x_854_);
lean_dec(v_i_848_);
v_i_848_ = v___x_855_;
goto _start;
}
else
{
lean_dec(v_i_848_);
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_keys_857_, lean_object* v_i_858_, lean_object* v_k_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_857_, v_i_858_, v_k_859_);
lean_dec_ref(v_k_859_);
lean_dec_ref(v_keys_857_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_862_, size_t v_x_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v_es_865_; lean_object* v___x_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v_j_869_; lean_object* v___x_870_; 
v_es_865_ = lean_ctor_get(v_x_862_, 0);
v___x_866_ = lean_box(2);
v___x_867_ = ((size_t)31ULL);
v___x_868_ = lean_usize_land(v_x_863_, v___x_867_);
v_j_869_ = lean_usize_to_nat(v___x_868_);
v___x_870_ = lean_array_get_borrowed(v___x_866_, v_es_865_, v_j_869_);
lean_dec(v_j_869_);
switch(lean_obj_tag(v___x_870_))
{
case 0:
{
lean_object* v_key_871_; uint8_t v___x_872_; 
v_key_871_ = lean_ctor_get(v___x_870_, 0);
v___x_872_ = l_Lean_instBEqExtraModUse_beq(v_x_864_, v_key_871_);
return v___x_872_;
}
case 1:
{
lean_object* v_node_873_; size_t v___x_874_; size_t v___x_875_; 
v_node_873_ = lean_ctor_get(v___x_870_, 0);
v___x_874_ = ((size_t)5ULL);
v___x_875_ = lean_usize_shift_right(v_x_863_, v___x_874_);
v_x_862_ = v_node_873_;
v_x_863_ = v___x_875_;
goto _start;
}
default: 
{
uint8_t v___x_877_; 
v___x_877_ = 0;
return v___x_877_;
}
}
}
else
{
lean_object* v_ks_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_ks_878_ = lean_ctor_get(v_x_862_, 0);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_ks_878_, v___x_879_, v_x_864_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_8325__boxed_884_; uint8_t v_res_885_; lean_object* v_r_886_; 
v_x_8325__boxed_884_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_881_, v_x_8325__boxed_884_, v_x_883_);
lean_dec_ref(v_x_883_);
lean_dec_ref(v_x_881_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
uint64_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v___x_889_ = l_Lean_instHashableExtraModUse_hash(v_x_888_);
v___x_890_ = lean_uint64_to_usize(v___x_889_);
v___x_891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_887_, v___x_890_, v_x_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_892_, v_x_893_);
lean_dec_ref(v_x_893_);
lean_dec_ref(v_x_892_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_896_; double v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_float_of_nat(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_cls_901_, lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_953_; 
v_ref_906_ = lean_ctor_get(v___y_903_, 2);
v___x_907_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_902_, v___y_903_, v___y_904_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_953_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_953_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_953_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v_traceState_913_; lean_object* v_env_914_; lean_object* v_nextMacroScope_915_; lean_object* v_ngen_916_; lean_object* v_auxDeclNGen_917_; lean_object* v_cache_918_; lean_object* v_recordedDeps_919_; lean_object* v_messages_920_; lean_object* v_infoState_921_; lean_object* v_snapshotTasks_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_952_; 
v___x_912_ = lean_st_ref_take(v___y_904_);
v_traceState_913_ = lean_ctor_get(v___x_912_, 4);
v_env_914_ = lean_ctor_get(v___x_912_, 0);
v_nextMacroScope_915_ = lean_ctor_get(v___x_912_, 1);
v_ngen_916_ = lean_ctor_get(v___x_912_, 2);
v_auxDeclNGen_917_ = lean_ctor_get(v___x_912_, 3);
v_cache_918_ = lean_ctor_get(v___x_912_, 5);
v_recordedDeps_919_ = lean_ctor_get(v___x_912_, 6);
v_messages_920_ = lean_ctor_get(v___x_912_, 7);
v_infoState_921_ = lean_ctor_get(v___x_912_, 8);
v_snapshotTasks_922_ = lean_ctor_get(v___x_912_, 9);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_952_ == 0)
{
v___x_924_ = v___x_912_;
v_isShared_925_ = v_isSharedCheck_952_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snapshotTasks_922_);
lean_inc(v_infoState_921_);
lean_inc(v_messages_920_);
lean_inc(v_recordedDeps_919_);
lean_inc(v_cache_918_);
lean_inc(v_traceState_913_);
lean_inc(v_auxDeclNGen_917_);
lean_inc(v_ngen_916_);
lean_inc(v_nextMacroScope_915_);
lean_inc(v_env_914_);
lean_dec(v___x_912_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_952_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
uint64_t v_tid_926_; lean_object* v_traces_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_951_; 
v_tid_926_ = lean_ctor_get_uint64(v_traceState_913_, sizeof(void*)*1);
v_traces_927_ = lean_ctor_get(v_traceState_913_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_traceState_913_);
if (v_isSharedCheck_951_ == 0)
{
v___x_929_ = v_traceState_913_;
v_isShared_930_ = v_isSharedCheck_951_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_traces_927_);
lean_dec(v_traceState_913_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_951_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; double v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_931_ = lean_box(0);
v___x_932_ = lean_box(0);
v___x_933_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_934_ = 0;
v___x_935_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_936_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_936_, 0, v_cls_901_);
lean_ctor_set(v___x_936_, 1, v___x_932_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_ctor_set_float(v___x_936_, sizeof(void*)*3, v___x_933_);
lean_ctor_set_float(v___x_936_, sizeof(void*)*3 + 8, v___x_933_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*3 + 16, v___x_934_);
v___x_937_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_938_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v_a_908_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
lean_inc(v_ref_906_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_ref_906_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_PersistentArray_push___redArg(v_traces_927_, v___x_939_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_940_);
v___x_942_ = v___x_929_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_940_);
lean_ctor_set_uint64(v_reuseFailAlloc_950_, sizeof(void*)*1, v_tid_926_);
v___x_942_ = v_reuseFailAlloc_950_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 4, v___x_942_);
v___x_944_ = v___x_924_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_env_914_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_nextMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_ngen_916_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_auxDeclNGen_917_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_949_, 5, v_cache_918_);
lean_ctor_set(v_reuseFailAlloc_949_, 6, v_recordedDeps_919_);
lean_ctor_set(v_reuseFailAlloc_949_, 7, v_messages_920_);
lean_ctor_set(v_reuseFailAlloc_949_, 8, v_infoState_921_);
lean_ctor_set(v_reuseFailAlloc_949_, 9, v_snapshotTasks_922_);
v___x_944_ = v_reuseFailAlloc_949_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_st_ref_put(v___y_904_, v___x_944_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_931_);
v___x_947_ = v___x_910_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_931_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_cls_954_, lean_object* v_msg_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_954_, v_msg_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_959_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v_cls_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_cls_979_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_980_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_981_ = l_Lean_Name_append(v___x_980_, v_cls_979_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_mod_992_, uint8_t v_isMeta_993_, lean_object* v_hint_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_env_1016_; uint8_t v_isExporting_1017_; lean_object* v_entry_1018_; lean_object* v___x_1019_; lean_object* v_env_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_1015_ = lean_st_ref_get(v___y_996_);
v_env_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc_ref(v_env_1016_);
lean_dec(v___x_1015_);
v_isExporting_1017_ = lean_ctor_get_uint8(v_env_1016_, sizeof(void*)*13);
lean_dec_ref(v_env_1016_);
lean_inc(v_mod_992_);
v_entry_1018_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1018_, 0, v_mod_992_);
lean_ctor_set_uint8(v_entry_1018_, sizeof(void*)*1, v_isExporting_1017_);
lean_ctor_set_uint8(v_entry_1018_, sizeof(void*)*1 + 1, v_isMeta_993_);
v___x_1019_ = lean_st_ref_get(v___y_996_);
v_env_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_env_1020_);
lean_dec(v___x_1019_);
v___x_1021_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1022_ = lean_box(1);
v___x_1023_ = lean_box(0);
v___x_1024_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1014_, v___x_1021_, v_env_1020_, v___x_1022_, v___x_1023_);
v___x_1025_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v___x_1024_, v_entry_1018_);
lean_dec(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v_toCold_1026_; lean_object* v_options_1027_; lean_object* v_inheritedTraceOptions_1028_; uint8_t v_hasTrace_1029_; lean_object* v___f_1030_; uint8_t v___x_1031_; lean_object* v___y_1033_; 
v_toCold_1026_ = lean_ctor_get(v___y_995_, 0);
v_options_1027_ = lean_ctor_get(v_toCold_1026_, 2);
v_inheritedTraceOptions_1028_ = lean_ctor_get(v_toCold_1026_, 11);
v_hasTrace_1029_ = lean_ctor_get_uint8(v_options_1027_, sizeof(void*)*1);
v___f_1030_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_1030_, 0, v___x_1021_);
lean_closure_set(v___f_1030_, 1, v_entry_1018_);
v___x_1031_ = 1;
if (v_hasTrace_1029_ == 0)
{
lean_dec(v_hint_994_);
lean_dec(v_mod_992_);
v___y_1033_ = v___y_996_;
goto v___jp_1032_;
}
else
{
lean_object* v_cls_1051_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_cls_1051_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_1071_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12);
v___x_1072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1028_, v_options_1027_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v_hint_994_);
lean_dec(v_mod_992_);
v___y_1033_ = v___y_996_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1073_; lean_object* v___y_1075_; 
v___x_1073_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14);
if (v_isExporting_1017_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19));
v___y_1075_ = v___x_1082_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20));
v___y_1075_ = v___x_1083_;
goto v___jp_1074_;
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_inc_ref(v___y_1075_);
v___x_1076_ = l_Lean_stringToMessageData(v___y_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1073_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
if (v_isMeta_993_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17));
v___y_1058_ = v___x_1079_;
v___y_1059_ = v___x_1080_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18));
v___y_1058_ = v___x_1079_;
v___y_1059_ = v___x_1081_;
goto v___jp_1057_;
}
}
}
v___jp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___y_1053_);
lean_ctor_set(v___x_1055_, 1, v___y_1054_);
v___x_1056_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_1051_, v___x_1055_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_dec_ref_known(v___x_1056_, 1);
v___y_1033_ = v___y_996_;
goto v___jp_1032_;
}
else
{
lean_dec_ref(v___f_1030_);
return v___x_1056_;
}
}
v___jp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
lean_inc_ref(v___y_1059_);
v___x_1060_ = l_Lean_stringToMessageData(v___y_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1058_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_MessageData_ofName(v_mod_992_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_Name_isAnonymous(v_hint_994_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8);
v___x_1068_ = l_Lean_MessageData_ofName(v_hint_994_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___y_1053_ = v___x_1065_;
v___y_1054_ = v___x_1069_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_hint_994_);
v___x_1070_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9);
v___y_1053_ = v___x_1065_;
v___y_1054_ = v___x_1070_;
goto v___jp_1052_;
}
}
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v_toEnvExtension_1035_; lean_object* v_env_1036_; lean_object* v_nextMacroScope_1037_; lean_object* v_ngen_1038_; lean_object* v_auxDeclNGen_1039_; lean_object* v_traceState_1040_; lean_object* v_recordedDeps_1041_; lean_object* v_messages_1042_; lean_object* v_infoState_1043_; lean_object* v_snapshotTasks_1044_; lean_object* v_asyncMode_1045_; uint8_t v_logWrites_1046_; lean_object* v___x_1047_; 
v___x_1034_ = lean_st_ref_take(v___y_1033_);
v_toEnvExtension_1035_ = lean_ctor_get(v___x_1021_, 0);
v_env_1036_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1036_);
v_nextMacroScope_1037_ = lean_ctor_get(v___x_1034_, 1);
lean_inc(v_nextMacroScope_1037_);
v_ngen_1038_ = lean_ctor_get(v___x_1034_, 2);
lean_inc_ref(v_ngen_1038_);
v_auxDeclNGen_1039_ = lean_ctor_get(v___x_1034_, 3);
lean_inc_ref(v_auxDeclNGen_1039_);
v_traceState_1040_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_traceState_1040_);
v_recordedDeps_1041_ = lean_ctor_get(v___x_1034_, 6);
lean_inc_ref(v_recordedDeps_1041_);
v_messages_1042_ = lean_ctor_get(v___x_1034_, 7);
lean_inc_ref(v_messages_1042_);
v_infoState_1043_ = lean_ctor_get(v___x_1034_, 8);
lean_inc_ref(v_infoState_1043_);
v_snapshotTasks_1044_ = lean_ctor_get(v___x_1034_, 9);
lean_inc_ref(v_snapshotTasks_1044_);
lean_dec(v___x_1034_);
v_asyncMode_1045_ = lean_ctor_get(v_toEnvExtension_1035_, 2);
v_logWrites_1046_ = lean_ctor_get_uint8(v_toEnvExtension_1035_, sizeof(void*)*6);
v___x_1047_ = lean_box(0);
if (v_logWrites_1046_ == 0)
{
lean_object* v___x_1048_; 
lean_inc_ref(v_toEnvExtension_1035_);
v___x_1048_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1035_, v_env_1036_, v___f_1030_, v_asyncMode_1045_, v___x_1023_, v___x_1031_);
v___y_999_ = v_traceState_1040_;
v___y_1000_ = v_messages_1042_;
v___y_1001_ = v_ngen_1038_;
v___y_1002_ = v_nextMacroScope_1037_;
v___y_1003_ = v_auxDeclNGen_1039_;
v___y_1004_ = v___x_1047_;
v___y_1005_ = v_infoState_1043_;
v___y_1006_ = v___y_1033_;
v___y_1007_ = v_snapshotTasks_1044_;
v___y_1008_ = v_recordedDeps_1041_;
v___y_1009_ = v___x_1048_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_inc_ref_n(v_toEnvExtension_1035_, 2);
v___x_1049_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1035_, v_env_1036_);
lean_dec_ref(v_env_1036_);
v___x_1050_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1035_, v___x_1049_, v___f_1030_, v_asyncMode_1045_, v___x_1023_, v___x_1031_);
v___y_999_ = v_traceState_1040_;
v___y_1000_ = v_messages_1042_;
v___y_1001_ = v_ngen_1038_;
v___y_1002_ = v_nextMacroScope_1037_;
v___y_1003_ = v_auxDeclNGen_1039_;
v___y_1004_ = v___x_1047_;
v___y_1005_ = v_infoState_1043_;
v___y_1006_ = v___y_1033_;
v___y_1007_ = v_snapshotTasks_1044_;
v___y_1008_ = v_recordedDeps_1041_;
v___y_1009_ = v___x_1050_;
goto v___jp_998_;
}
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref_known(v_entry_1018_, 1);
lean_dec(v_hint_994_);
lean_dec(v_mod_992_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
v___jp_998_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_1011_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1011_, 0, v___y_1009_);
lean_ctor_set(v___x_1011_, 1, v___y_1002_);
lean_ctor_set(v___x_1011_, 2, v___y_1001_);
lean_ctor_set(v___x_1011_, 3, v___y_1003_);
lean_ctor_set(v___x_1011_, 4, v___y_999_);
lean_ctor_set(v___x_1011_, 5, v___x_1010_);
lean_ctor_set(v___x_1011_, 6, v___y_1008_);
lean_ctor_set(v___x_1011_, 7, v___y_1000_);
lean_ctor_set(v___x_1011_, 8, v___y_1005_);
lean_ctor_set(v___x_1011_, 9, v___y_1007_);
v___x_1012_ = lean_st_ref_put(v___y_1006_, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___y_1004_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_mod_1086_, lean_object* v_isMeta_1087_, lean_object* v_hint_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v_isMeta_boxed_1092_; lean_object* v_res_1093_; 
v_isMeta_boxed_1092_ = lean_unbox(v_isMeta_1087_);
v_res_1093_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_mod_1086_, v_isMeta_boxed_1092_, v_hint_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object* v___x_1094_, lean_object* v_declName_1095_, lean_object* v_as_1096_, size_t v_sz_1097_, size_t v_i_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1098_, v_sz_1097_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec(v_declName_1095_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_b_1099_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v_modules_1106_; lean_object* v___x_1107_; lean_object* v_a_1108_; lean_object* v___x_1109_; lean_object* v_toImport_1110_; lean_object* v_module_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1105_ = l_Lean_Environment_header(v___x_1094_);
v_modules_1106_ = lean_ctor_get(v___x_1105_, 3);
lean_inc_ref(v_modules_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1108_ = lean_array_uget_borrowed(v_as_1096_, v_i_1098_);
v___x_1109_ = lean_array_get(v___x_1107_, v_modules_1106_, v_a_1108_);
lean_dec_ref(v_modules_1106_);
v_toImport_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_toImport_1110_);
lean_dec(v___x_1109_);
v_module_1111_ = lean_ctor_get(v_toImport_1110_, 0);
lean_inc(v_module_1111_);
lean_dec_ref(v_toImport_1110_);
v___x_1112_ = lean_box(0);
v___x_1113_ = 0;
lean_inc(v_declName_1095_);
v___x_1114_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1111_, v___x_1113_, v_declName_1095_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1114_) == 0)
{
size_t v___x_1115_; size_t v___x_1116_; 
lean_dec_ref_known(v___x_1114_, 1);
v___x_1115_ = ((size_t)1ULL);
v___x_1116_ = lean_usize_add(v_i_1098_, v___x_1115_);
v_i_1098_ = v___x_1116_;
v_b_1099_ = v___x_1112_;
goto _start;
}
else
{
lean_dec(v_declName_1095_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v___x_1118_, lean_object* v_declName_1119_, lean_object* v_as_1120_, lean_object* v_sz_1121_, lean_object* v_i_1122_, lean_object* v_b_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1121_);
lean_dec(v_sz_1121_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v___x_1118_, v_declName_1119_, v_as_1120_, v_sz_boxed_1127_, v_i_boxed_1128_, v_b_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_as_1120_);
lean_dec_ref(v___x_1118_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(lean_object* v_declName_1133_, uint8_t v_isMeta_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_env_1143_; lean_object* v___y_1145_; lean_object* v___x_1158_; 
v___x_1138_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0);
v___x_1139_ = lean_st_ref_get(v___y_1136_);
v_env_1143_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1139_);
v___x_1158_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1143_, v_declName_1133_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_dec_ref(v_env_1143_);
lean_dec(v_declName_1133_);
goto v___jp_1140_;
}
else
{
lean_object* v_val_1159_; lean_object* v___x_1160_; lean_object* v_modules_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_val_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_Environment_header(v_env_1143_);
v_modules_1161_ = lean_ctor_get(v___x_1160_, 3);
lean_inc_ref(v_modules_1161_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = lean_array_get_size(v_modules_1161_);
v___x_1163_ = lean_nat_dec_lt(v_val_1159_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec_ref(v_modules_1161_);
lean_dec(v_val_1159_);
lean_dec_ref(v_env_1143_);
lean_dec(v_declName_1133_);
goto v___jp_1140_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___y_1167_; 
v___x_1164_ = lean_array_fget(v_modules_1161_, v_val_1159_);
lean_dec(v_val_1159_);
lean_dec_ref(v_modules_1161_);
v___x_1165_ = lean_st_ref_get(v___y_1136_);
if (v_isMeta_1134_ == 0)
{
lean_dec(v___x_1165_);
v___y_1167_ = v_isMeta_1134_;
goto v___jp_1166_;
}
else
{
lean_object* v_env_1178_; uint8_t v___x_1179_; 
v_env_1178_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref(v_env_1178_);
lean_dec(v___x_1165_);
lean_inc(v_declName_1133_);
v___x_1179_ = l_Lean_isMarkedMeta(v_env_1178_, v_declName_1133_);
if (v___x_1179_ == 0)
{
v___y_1167_ = v_isMeta_1134_;
goto v___jp_1166_;
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = 0;
v___y_1167_ = v___x_1180_;
goto v___jp_1166_;
}
}
v___jp_1166_:
{
lean_object* v_toImport_1168_; lean_object* v_module_1169_; lean_object* v___x_1170_; 
v_toImport_1168_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_toImport_1168_);
lean_dec(v___x_1164_);
v_module_1169_ = lean_ctor_get(v_toImport_1168_, 0);
lean_inc(v_module_1169_);
lean_dec_ref(v_toImport_1168_);
lean_inc(v_declName_1133_);
v___x_1170_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1169_, v___y_1167_, v_declName_1133_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref_known(v___x_1170_, 1);
v___x_1171_ = l_Lean_indirectModUseExt;
v___x_1172_ = lean_box(1);
v___x_1173_ = lean_box(0);
lean_inc_ref(v_env_1143_);
v___x_1174_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1138_, v___x_1171_, v_env_1143_, v___x_1172_, v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v___x_1174_, v_declName_1133_);
lean_dec(v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1));
v___y_1145_ = v___x_1176_;
goto v___jp_1144_;
}
else
{
lean_object* v_val_1177_; 
v_val_1177_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v___x_1175_, 1);
v___y_1145_ = v_val_1177_;
goto v___jp_1144_;
}
}
else
{
lean_dec_ref(v_env_1143_);
lean_dec(v_declName_1133_);
return v___x_1170_;
}
}
}
}
v___jp_1140_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
v___jp_1144_:
{
lean_object* v___x_1146_; size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v___x_1146_ = lean_box(0);
v_sz_1147_ = lean_array_size(v___y_1145_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v_env_1143_, v_declName_1133_, v___y_1145_, v_sz_1147_, v___x_1148_, v___x_1146_, v___y_1135_, v___y_1136_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_env_1143_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1157_);
v___x_1151_ = v___x_1149_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v___x_1149_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1146_);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1146_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
return v___x_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1181_, lean_object* v_isMeta_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_isMeta_boxed_1186_; lean_object* v_res_1187_; 
v_isMeta_boxed_1186_ = lean_unbox(v_isMeta_1182_);
v_res_1187_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_declName_1181_, v_isMeta_boxed_1186_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1187_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = lean_box(1);
v___x_1197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_1198_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1197_);
lean_ctor_set(v___x_1199_, 2, v___x_1196_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_x_1200_, lean_object* v_stx_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1288_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1288_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1288_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_infoState_1212_; uint8_t v_enabled_1213_; 
v___x_1210_ = l_Lean_Syntax_getId(v_a_1206_);
v___x_1211_ = lean_st_ref_get(v___y_1203_);
v_infoState_1212_ = lean_ctor_get(v___x_1211_, 8);
lean_inc_ref(v_infoState_1212_);
lean_dec(v___x_1211_);
v_enabled_1213_ = lean_ctor_get_uint8(v_infoState_1212_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1212_);
if (v_enabled_1213_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1215_ = v___x_1208_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = l_Lean_Name_isAtomic(v___x_1210_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = l_Lean_Name_getRoot(v___x_1210_);
v___x_1219_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1220_ = lean_name_eq(v___x_1218_, v___x_1219_);
lean_dec(v___x_1218_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1222_ = v___x_1208_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1210_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___y_1227_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_del_object(v___x_1208_);
v___x_1224_ = lean_box(0);
lean_inc(v___x_1210_);
v___x_1225_ = l_Lean_Name_replacePrefix(v___x_1210_, v___x_1219_, v___x_1224_);
v___x_1282_ = lean_box(0);
v___x_1283_ = l_Lean_Syntax_identComponents(v_a_1206_, v___x_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
v___y_1227_ = v___x_1283_;
goto v___jp_1226_;
}
else
{
lean_object* v_tail_1284_; 
v_tail_1284_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_tail_1284_);
lean_dec_ref_known(v___x_1283_, 2);
v___y_1227_ = v_tail_1284_;
goto v___jp_1226_;
}
v___jp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1228_ = lean_array_mk(v___y_1227_);
v___x_1229_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1230_ = lean_box(2);
v___x_1231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1229_);
lean_ctor_set(v___x_1231_, 2, v___x_1228_);
lean_inc_n(v___x_1225_, 2);
v___x_1232_ = l_Lean_mkIdentFrom(v___x_1231_, v___x_1225_, v_enabled_1213_);
lean_dec_ref_known(v___x_1231_, 3);
v___x_1233_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1234_ = lean_box(0);
lean_inc(v___x_1232_);
v___x_1235_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1235_, 0, v___x_1232_);
lean_ctor_set(v___x_1235_, 1, v___x_1225_);
lean_ctor_set(v___x_1235_, 2, v___x_1233_);
lean_ctor_set(v___x_1235_, 3, v___x_1234_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*4, v___x_1217_);
v___x_1236_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v___x_1235_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1272_; 
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1273_);
v___x_1238_ = v___x_1236_;
v_isShared_1239_ = v_isSharedCheck_1272_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1272_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v_env_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_st_ref_get(v___y_1203_);
v_env_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc_ref(v_env_1241_);
lean_dec(v___x_1240_);
lean_inc(v___x_1225_);
v___x_1242_ = l_Lean_Environment_contains(v_env_1241_, v___x_1225_, v_enabled_1213_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v___x_1232_);
lean_dec(v___x_1225_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1210_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1210_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1246_; 
lean_del_object(v___x_1238_);
lean_inc(v___x_1225_);
v___x_1246_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v___x_1225_, v___x_1217_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1246_, 1);
v___x_1247_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v___x_1232_, v___x_1225_, v___x_1234_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1255_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1210_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1210_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___x_1210_);
v_a_1256_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1247_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1247_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___x_1232_);
lean_dec(v___x_1225_);
lean_dec(v___x_1210_);
v_a_1264_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1246_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1246_);
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
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v___x_1232_);
lean_dec(v___x_1225_);
lean_dec(v___x_1210_);
v_a_1274_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1236_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1236_);
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
}
}
else
{
lean_object* v___x_1286_; 
lean_dec(v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1286_ = v___x_1208_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1210_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1205_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1205_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_x_1297_, lean_object* v_stx_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_x_8886__boxed_1302_; lean_object* v_res_1303_; 
v_x_8886__boxed_1302_ = lean_unbox(v_x_1297_);
v_res_1303_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_x_8886__boxed_1302_, v_stx_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1337_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1338_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1336_, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_t_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_1341_, v___y_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_t_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_t_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1351_, lean_object* v_m_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_1352_, v_a_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1355_, lean_object* v_m_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1355_, v_m_1356_, v_a_1357_);
lean_dec(v_a_1357_);
lean_dec_ref(v_m_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_1360_, v_x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_1363_, v_x_1364_, v_x_1365_);
lean_dec_ref(v_x_1365_);
lean_dec_ref(v_x_1364_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1368_, lean_object* v_a_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_1369_, v_x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1372_, lean_object* v_a_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_00_u03b2_1372_, v_a_1373_, v_x_1374_);
lean_dec(v_x_1374_);
lean_dec(v_a_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1376_, lean_object* v_x_1377_, size_t v_x_1378_, lean_object* v_x_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_1377_, v_x_1378_, v_x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
size_t v_x_9221__boxed_1385_; uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_x_9221__boxed_1385_ = lean_unbox_usize(v_x_1383_);
lean_dec(v_x_1383_);
v_res_1386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1381_, v_x_1382_, v_x_9221__boxed_1385_, v_x_1384_);
lean_dec_ref(v_x_1384_);
lean_dec_ref(v_x_1382_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object* v_00_u03b1_1388_, lean_object* v_constName_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_1389_, v___y_1390_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(v_00_u03b1_1394_, v_constName_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1400_, lean_object* v_keys_1401_, lean_object* v_vals_1402_, lean_object* v_heq_1403_, lean_object* v_i_1404_, lean_object* v_k_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_1401_, v_i_1404_, v_k_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1407_, lean_object* v_keys_1408_, lean_object* v_vals_1409_, lean_object* v_heq_1410_, lean_object* v_i_1411_, lean_object* v_k_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(v_00_u03b2_1407_, v_keys_1408_, v_vals_1409_, v_heq_1410_, v_i_1411_, v_k_1412_);
lean_dec_ref(v_k_1412_);
lean_dec_ref(v_vals_1409_);
lean_dec_ref(v_keys_1408_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object* v_00_u03b1_1415_, lean_object* v_ref_1416_, lean_object* v_constName_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_1416_, v_constName_1417_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1422_, lean_object* v_ref_1423_, lean_object* v_constName_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_1422_, v_ref_1423_, v_constName_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v_ref_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1429_, lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v_declHint_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_1430_, v_msg_1431_, v_declHint_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_msg_1439_, lean_object* v_declHint_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(v_00_u03b1_1437_, v_ref_1438_, v_msg_1439_, v_declHint_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v_ref_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1445_, lean_object* v_declHint_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1445_, v_declHint_1446_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1451_, lean_object* v_declHint_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(v_msg_1451_, v_declHint_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1457_, lean_object* v_ref_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_1458_, v_msg_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_1464_, v_ref_1465_, v_msg_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_ref_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1477_, v_msg_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1486_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1487_ = l_Lean_addBuiltinDocString(v___x_1485_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1517_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1518_ = l_Lean_addBuiltinDeclarationRanges(v___x_1516_, v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1549_, uint8_t v___x_1550_, lean_object* v_id_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1549_, v___x_1550_);
v___x_1557_ = lean_string_append(v___x_1555_, v___x_1556_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1559_ = lean_string_append(v___x_1557_, v___x_1558_);
v___x_1560_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1551_, v___x_1559_, v___y_1553_, v___y_1554_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_id_1563_, lean_object* v_x_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v___x_2296__boxed_1567_; lean_object* v_res_1568_; 
v___x_2296__boxed_1567_ = lean_unbox(v___x_1562_);
v_res_1568_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1561_, v___x_2296__boxed_1567_, v_id_1563_, v_x_1564_, v___y_1565_, v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v_x_1564_);
lean_dec(v_id_1563_);
return v_res_1568_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1579_ = l_String_toRawSubstring_x27(v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___y_1584_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1580_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_x_1580_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_x_1580_);
v___x_1605_ = lean_box(1);
v___x_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v_a_1582_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v_id_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = lean_unsigned_to_nat(1u);
v_id_1608_ = l_Lean_Syntax_getArg(v_x_1580_, v___x_1607_);
lean_dec(v_x_1580_);
v___x_1609_ = l_Lean_TSyntax_getId(v_id_1608_);
lean_inc(v___x_1609_);
v___x_1610_ = l_Lean_Macro_resolveGlobalName(v___x_1609_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
if (lean_obj_tag(v_a_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_a_1612_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1610_, 2);
v___x_1613_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1614_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1609_, v___x_1604_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
v___x_1618_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1608_, v___x_1617_, v_a_1581_, v_a_1612_);
lean_dec(v_id_1608_);
v___y_1584_ = v___x_1618_;
goto v___jp_1583_;
}
else
{
lean_object* v_head_1619_; lean_object* v_snd_1620_; 
v_head_1619_ = lean_ctor_get(v_a_1611_, 0);
v_snd_1620_ = lean_ctor_get(v_head_1619_, 1);
if (lean_obj_tag(v_snd_1620_) == 0)
{
lean_object* v_tail_1621_; 
v_tail_1621_ = lean_ctor_get(v_a_1611_, 1);
if (lean_obj_tag(v_tail_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1647_; 
lean_inc(v_head_1619_);
lean_dec(v___x_1609_);
v_a_1622_ = lean_ctor_get(v___x_1610_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1610_, 0);
lean_dec(v_unused_1648_);
v___x_1624_ = v___x_1610_;
v_isShared_1625_ = v_isSharedCheck_1647_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1610_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1647_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_fst_1626_; lean_object* v_quotContext_1627_; lean_object* v_currMacroScope_1628_; lean_object* v_ref_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v_fst_1626_ = lean_ctor_get(v_head_1619_, 0);
lean_inc(v_fst_1626_);
lean_dec(v_head_1619_);
v_quotContext_1627_ = lean_ctor_get(v_a_1581_, 1);
v_currMacroScope_1628_ = lean_ctor_get(v_a_1581_, 2);
v_ref_1629_ = lean_ctor_get(v_a_1581_, 5);
v___x_1630_ = 0;
v___x_1631_ = l_Lean_SourceInfo_fromRef(v_ref_1629_, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1633_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1634_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1628_);
lean_inc(v_quotContext_1627_);
v___x_1635_ = l_Lean_addMacroScope(v_quotContext_1627_, v___x_1634_, v_currMacroScope_1628_);
v___x_1636_ = lean_box(0);
lean_inc_n(v___x_1631_, 2);
v___x_1637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1631_);
lean_ctor_set(v___x_1637_, 1, v___x_1633_);
lean_ctor_set(v___x_1637_, 2, v___x_1635_);
lean_ctor_set(v___x_1637_, 3, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1639_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1640_ = l_Lean_Name_append(v___x_1639_, v_fst_1626_);
v___x_1641_ = l_Lean_mkIdentFrom(v_id_1608_, v___x_1640_, v___x_1604_);
lean_dec(v_id_1608_);
v___x_1642_ = l_Lean_Syntax_node1(v___x_1631_, v___x_1638_, v___x_1641_);
v___x_1643_ = l_Lean_Syntax_node2(v___x_1631_, v___x_1632_, v___x_1637_, v___x_1642_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1643_);
v___x_1645_ = v___x_1624_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1622_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v_a_1611_);
v_a_1649_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1610_, 2);
v___x_1650_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1609_, v___x_1604_, v_id_1608_, v_a_1611_, v_a_1581_, v_a_1649_);
lean_dec_ref_known(v_a_1611_, 2);
lean_dec(v_id_1608_);
v___y_1584_ = v___x_1650_;
goto v___jp_1583_;
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1652_; 
lean_inc_ref(v_a_1611_);
v_a_1651_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1610_, 2);
v___x_1652_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1609_, v___x_1604_, v_id_1608_, v_a_1611_, v_a_1581_, v_a_1651_);
lean_dec_ref_known(v_a_1611_, 2);
lean_dec(v_id_1608_);
v___y_1584_ = v___x_1652_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v___x_1609_);
lean_dec(v_id_1608_);
v_a_1653_ = lean_ctor_get(v___x_1610_, 0);
v_a_1654_ = lean_ctor_get(v___x_1610_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1610_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_inc(v_a_1653_);
lean_dec(v___x_1610_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
v___jp_1583_:
{
if (lean_obj_tag(v___y_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1585_ = lean_ctor_get(v___y_1584_, 0);
v_a_1586_ = lean_ctor_get(v___y_1584_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___y_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___y_1584_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_inc(v_a_1585_);
lean_dec(v___y_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1585_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_a_1594_ = lean_ctor_get(v___y_1584_, 0);
v_a_1595_ = lean_ctor_get(v___y_1584_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___y_1584_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___y_1584_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_inc(v_a_1594_);
lean_dec(v___y_1584_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1594_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1662_, v_a_1663_, v_a_1664_);
lean_dec_ref(v_a_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1666_){
_start:
{
lean_object* v_subExpr_1668_; lean_object* v_expr_1669_; lean_object* v___x_1670_; 
v_subExpr_1668_ = lean_ctor_get(v___y_1666_, 3);
v_expr_1669_ = lean_ctor_get(v_subExpr_1668_, 0);
lean_inc_ref(v_expr_1669_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_expr_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1671_);
lean_dec_ref(v___y_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1674_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1690_, lean_object* v_us_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1693_ = l_Lean_Name_append(v___x_1692_, v_c_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1694_, lean_object* v_us_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1694_, v_us_1695_);
lean_dec(v_us_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1702_);
lean_dec(v_x_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1814_; 
v___x_1738_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1731_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1814_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1814_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
switch(lean_obj_tag(v_a_1739_))
{
case 0:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec_ref_known(v_a_1739_, 1);
v___x_1743_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1745_ = v___x_1741_;
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
case 1:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec_ref_known(v_a_1739_, 1);
v___x_1747_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1747_);
v___x_1749_ = v___x_1741_;
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
case 2:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_dec_ref_known(v_a_1739_, 1);
v___x_1751_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1751_);
v___x_1753_ = v___x_1741_;
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
case 3:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref_known(v_a_1739_, 1);
v___x_1755_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1755_);
v___x_1757_ = v___x_1741_;
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
case 4:
{
lean_object* v_declName_1759_; lean_object* v_us_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v_declName_1759_ = lean_ctor_get(v_a_1739_, 0);
lean_inc(v_declName_1759_);
v_us_1760_ = lean_ctor_get(v_a_1739_, 1);
lean_inc(v_us_1760_);
lean_dec_ref_known(v_a_1739_, 2);
v___x_1761_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1759_, v_us_1760_);
lean_dec(v_us_1760_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1761_);
v___x_1763_ = v___x_1741_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
case 5:
{
lean_object* v_fn_1765_; lean_object* v___x_1766_; 
v_fn_1765_ = lean_ctor_get(v_a_1739_, 0);
lean_inc_ref(v_fn_1765_);
lean_dec_ref_known(v_a_1739_, 2);
v___x_1766_ = l_Lean_Expr_getAppFn(v_fn_1765_);
lean_dec_ref(v_fn_1765_);
if (lean_obj_tag(v___x_1766_) == 4)
{
lean_object* v_declName_1767_; lean_object* v_us_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_declName_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_declName_1767_);
v_us_1768_ = lean_ctor_get(v___x_1766_, 1);
lean_inc(v_us_1768_);
lean_dec_ref_known(v___x_1766_, 2);
v___x_1769_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1767_, v_us_1768_);
lean_dec(v_us_1768_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1769_);
v___x_1771_ = v___x_1741_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
lean_dec_ref(v___x_1766_);
v___x_1773_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1773_);
v___x_1775_ = v___x_1741_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
case 6:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec_ref_known(v_a_1739_, 3);
v___x_1777_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1777_);
v___x_1779_ = v___x_1741_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
case 7:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec_ref_known(v_a_1739_, 3);
v___x_1781_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1781_);
v___x_1783_ = v___x_1741_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
case 8:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec_ref_known(v_a_1739_, 4);
v___x_1785_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1785_);
v___x_1787_ = v___x_1741_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
case 9:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec_ref_known(v_a_1739_, 1);
v___x_1789_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1789_);
v___x_1791_ = v___x_1741_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
case 10:
{
lean_object* v_data_1793_; 
v_data_1793_ = lean_ctor_get(v_a_1739_, 0);
lean_inc(v_data_1793_);
lean_dec_ref_known(v_a_1739_, 2);
if (lean_obj_tag(v_data_1793_) == 1)
{
lean_object* v_tail_1794_; 
v_tail_1794_ = lean_ctor_get(v_data_1793_, 1);
if (lean_obj_tag(v_tail_1794_) == 0)
{
lean_object* v_head_1795_; lean_object* v_fst_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v_head_1795_ = lean_ctor_get(v_data_1793_, 0);
lean_inc(v_head_1795_);
lean_dec_ref_known(v_data_1793_, 2);
v_fst_1796_ = lean_ctor_get(v_head_1795_, 0);
lean_inc(v_fst_1796_);
lean_dec(v_head_1795_);
v___x_1797_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1798_ = l_Lean_Name_append(v___x_1797_, v_fst_1796_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1798_);
v___x_1800_ = v___x_1741_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1793_);
lean_dec_ref_known(v_data_1793_, 2);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1802_);
v___x_1804_ = v___x_1741_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1793_);
lean_dec(v_data_1793_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1806_);
v___x_1808_ = v___x_1741_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
default: 
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_dec_ref_known(v_a_1739_, 3);
v___x_1810_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1810_);
v___x_1812_ = v___x_1741_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1823_, lean_object* v_k_1824_, lean_object* v_v_1825_){
_start:
{
lean_object* v_map_1826_; uint8_t v_hasTrace_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1840_; 
v_map_1826_ = lean_ctor_get(v_o_1823_, 0);
v_hasTrace_1827_ = lean_ctor_get_uint8(v_o_1823_, sizeof(void*)*1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_o_1823_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1829_ = v_o_1823_;
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_map_1826_);
lean_dec(v_o_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; 
lean_inc(v_k_1824_);
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1824_, v_v_1825_, v_map_1826_);
if (v_hasTrace_1827_ == 0)
{
lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1835_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_1833_ = l_Lean_Name_isPrefixOf(v___x_1832_, v_k_1824_);
lean_dec(v_k_1824_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1831_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*1, v___x_1833_);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_k_1824_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1838_ = v___x_1829_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*1, v_hasTrace_1827_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1841_){
_start:
{
lean_object* v_subExpr_1843_; lean_object* v_pos_1844_; lean_object* v___x_1845_; 
v_subExpr_1843_ = lean_ctor_get(v___y_1841_, 3);
v_pos_1844_ = lean_ctor_get(v_subExpr_1843_, 1);
lean_inc(v_pos_1844_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_pos_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1846_);
lean_dec_ref(v___y_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1849_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1865_, lean_object* v_k_1866_){
_start:
{
if (lean_obj_tag(v_t_1865_) == 0)
{
lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v_l_1869_; lean_object* v_r_1870_; uint8_t v___x_1871_; 
v_k_1867_ = lean_ctor_get(v_t_1865_, 1);
v_v_1868_ = lean_ctor_get(v_t_1865_, 2);
v_l_1869_ = lean_ctor_get(v_t_1865_, 3);
v_r_1870_ = lean_ctor_get(v_t_1865_, 4);
v___x_1871_ = lean_nat_dec_lt(v_k_1866_, v_k_1867_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_eq(v_k_1866_, v_k_1867_);
if (v___x_1872_ == 0)
{
v_t_1865_ = v_r_1870_;
goto _start;
}
else
{
lean_object* v___x_1874_; 
lean_inc(v_v_1868_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_v_1868_);
return v___x_1874_;
}
}
else
{
v_t_1865_ = v_l_1869_;
goto _start;
}
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_box(0);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1877_, lean_object* v_k_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1877_, v_k_1878_);
lean_dec(v_k_1878_);
lean_dec(v_t_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1881_) == 0)
{
lean_object* v_k_1883_; lean_object* v_v_1884_; lean_object* v_l_1885_; lean_object* v_r_1886_; lean_object* v___x_1887_; lean_object* v_a_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_k_1883_ = lean_ctor_get(v_x_1881_, 1);
lean_inc(v_k_1883_);
v_v_1884_ = lean_ctor_get(v_x_1881_, 2);
lean_inc(v_v_1884_);
v_l_1885_ = lean_ctor_get(v_x_1881_, 3);
lean_inc(v_l_1885_);
v_r_1886_ = lean_ctor_get(v_x_1881_, 4);
lean_inc(v_r_1886_);
lean_dec_ref_known(v_x_1881_, 5);
v___x_1887_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1880_, v_l_1885_);
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v_a_1889_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_a_1889_);
lean_dec(v_a_1888_);
v___x_1890_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1889_, v_k_1883_, v_v_1884_);
v_init_1880_ = v___x_1890_;
v_x_1881_ = v_r_1886_;
goto _start;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_init_1880_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1894_, lean_object* v_x_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1894_, v_x_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1928_; 
v___x_1905_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1902_);
v___x_1906_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1898_);
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_optionsPerPos_1911_; lean_object* v___x_1912_; 
v_optionsPerPos_1911_ = lean_ctor_get(v_a_1898_, 0);
v___x_1912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1911_, v_a_1907_);
lean_dec(v_a_1907_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v_map_1914_; lean_object* v___x_1915_; lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1909_);
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v_map_1914_ = lean_ctor_get(v_val_1913_, 0);
lean_inc(v_map_1914_);
lean_dec(v_val_1913_);
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v___x_1905_, v_map_1914_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_a_1920_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v_a_1916_, 0);
lean_inc(v_a_1920_);
lean_dec(v_a_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_a_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v___x_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1905_);
v___x_1926_ = v___x_1909_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1905_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1937_, lean_object* v_t_1938_, lean_object* v_k_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1938_, v_k_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1941_, lean_object* v_t_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1941_, v_t_1942_, v_k_1943_);
lean_dec(v_k_1943_);
lean_dec(v_t_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1945_, v_x_1946_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1955_, v_x_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_apply_1(v_opt_1965_, v_a_1974_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_opt_1965_);
v_a_1983_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1973_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1973_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_2000_, lean_object* v_opt_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_opt_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_2010_, v_opt_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_2020_, lean_object* v_d_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2020_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; uint8_t v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
lean_dec_ref(v_d_2021_);
v___x_2032_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
lean_inc(v_a_2027_);
lean_inc_ref(v_a_2026_);
lean_inc(v_a_2025_);
lean_inc_ref(v_a_2024_);
lean_inc(v_a_2023_);
lean_inc_ref(v_a_2022_);
v___x_2033_ = lean_apply_7(v_d_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, lean_box(0));
return v___x_2033_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_d_2021_);
v_a_2034_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2029_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2042_, lean_object* v_d_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2042_, v_d_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2052_, lean_object* v_d_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2052_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; uint8_t v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_unbox(v_a_2062_);
lean_dec(v_a_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_inc(v_a_2059_);
lean_inc_ref(v_a_2058_);
lean_inc(v_a_2057_);
lean_inc_ref(v_a_2056_);
lean_inc(v_a_2055_);
lean_inc_ref(v_a_2054_);
v___x_2064_ = lean_apply_7(v_d_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, lean_box(0));
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v_d_2053_);
v___x_2065_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2065_;
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_d_2053_);
v_a_2066_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2061_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2061_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2074_, lean_object* v_d_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2074_, v_d_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2084_, lean_object* v_v_2085_, lean_object* v_t_2086_){
_start:
{
if (lean_obj_tag(v_t_2086_) == 0)
{
lean_object* v_size_2087_; lean_object* v_k_2088_; lean_object* v_v_2089_; lean_object* v_l_2090_; lean_object* v_r_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2372_; 
v_size_2087_ = lean_ctor_get(v_t_2086_, 0);
v_k_2088_ = lean_ctor_get(v_t_2086_, 1);
v_v_2089_ = lean_ctor_get(v_t_2086_, 2);
v_l_2090_ = lean_ctor_get(v_t_2086_, 3);
v_r_2091_ = lean_ctor_get(v_t_2086_, 4);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_t_2086_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2093_ = v_t_2086_;
v_isShared_2094_ = v_isSharedCheck_2372_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_r_2091_);
lean_inc(v_l_2090_);
lean_inc(v_v_2089_);
lean_inc(v_k_2088_);
lean_inc(v_size_2087_);
lean_dec(v_t_2086_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2372_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v_k_2084_, v_k_2088_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_eq(v_k_2084_, v_k_2088_);
if (v___x_2096_ == 0)
{
lean_object* v_impl_2097_; lean_object* v___x_2098_; 
lean_dec(v_size_2087_);
v_impl_2097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2084_, v_v_2085_, v_r_2091_);
v___x_2098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2090_) == 0)
{
lean_object* v_size_2099_; lean_object* v_size_2100_; lean_object* v_k_2101_; lean_object* v_v_2102_; lean_object* v_l_2103_; lean_object* v_r_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_size_2099_ = lean_ctor_get(v_l_2090_, 0);
v_size_2100_ = lean_ctor_get(v_impl_2097_, 0);
v_k_2101_ = lean_ctor_get(v_impl_2097_, 1);
v_v_2102_ = lean_ctor_get(v_impl_2097_, 2);
v_l_2103_ = lean_ctor_get(v_impl_2097_, 3);
lean_inc(v_l_2103_);
v_r_2104_ = lean_ctor_get(v_impl_2097_, 4);
v___x_2105_ = lean_unsigned_to_nat(3u);
v___x_2106_ = lean_nat_mul(v___x_2105_, v_size_2099_);
v___x_2107_ = lean_nat_dec_lt(v___x_2106_, v_size_2100_);
lean_dec(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
lean_dec(v_l_2103_);
v___x_2108_ = lean_nat_add(v___x_2098_, v_size_2099_);
v___x_2109_ = lean_nat_add(v___x_2108_, v_size_2100_);
lean_dec(v___x_2108_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_impl_2097_);
lean_ctor_set(v___x_2093_, 0, v___x_2109_);
v___x_2111_ = v___x_2093_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_l_2090_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_impl_2097_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
else
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2176_; 
lean_inc(v_r_2104_);
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
lean_inc(v_size_2100_);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_impl_2097_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; lean_object* v_unused_2178_; lean_object* v_unused_2179_; lean_object* v_unused_2180_; lean_object* v_unused_2181_; 
v_unused_2177_ = lean_ctor_get(v_impl_2097_, 4);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_impl_2097_, 3);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_impl_2097_, 2);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_impl_2097_, 1);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_impl_2097_, 0);
lean_dec(v_unused_2181_);
v___x_2114_ = v_impl_2097_;
v_isShared_2115_ = v_isSharedCheck_2176_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v_impl_2097_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2176_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_size_2116_; lean_object* v_k_2117_; lean_object* v_v_2118_; lean_object* v_l_2119_; lean_object* v_r_2120_; lean_object* v_size_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_size_2116_ = lean_ctor_get(v_l_2103_, 0);
v_k_2117_ = lean_ctor_get(v_l_2103_, 1);
v_v_2118_ = lean_ctor_get(v_l_2103_, 2);
v_l_2119_ = lean_ctor_get(v_l_2103_, 3);
v_r_2120_ = lean_ctor_get(v_l_2103_, 4);
v_size_2121_ = lean_ctor_get(v_r_2104_, 0);
v___x_2122_ = lean_unsigned_to_nat(2u);
v___x_2123_ = lean_nat_mul(v___x_2122_, v_size_2121_);
v___x_2124_ = lean_nat_dec_lt(v_size_2116_, v___x_2123_);
lean_dec(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2152_; 
lean_inc(v_r_2120_);
lean_inc(v_l_2119_);
lean_inc(v_v_2118_);
lean_inc(v_k_2117_);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_l_2103_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2153_ = lean_ctor_get(v_l_2103_, 4);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_l_2103_, 3);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_l_2103_, 2);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_l_2103_, 1);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_2103_, 0);
lean_dec(v_unused_2157_);
v___x_2126_ = v_l_2103_;
v_isShared_2127_ = v_isSharedCheck_2152_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v_l_2103_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2152_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2142_; 
v___x_2128_ = lean_nat_add(v___x_2098_, v_size_2099_);
v___x_2129_ = lean_nat_add(v___x_2128_, v_size_2100_);
lean_dec(v_size_2100_);
if (lean_obj_tag(v_l_2119_) == 0)
{
lean_object* v_size_2150_; 
v_size_2150_ = lean_ctor_get(v_l_2119_, 0);
lean_inc(v_size_2150_);
v___y_2142_ = v_size_2150_;
goto v___jp_2141_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_unsigned_to_nat(0u);
v___y_2142_ = v___x_2151_;
goto v___jp_2141_;
}
v___jp_2130_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_nat_add(v___y_2131_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec(v___y_2131_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 4, v_r_2104_);
lean_ctor_set(v___x_2126_, 3, v_r_2120_);
lean_ctor_set(v___x_2126_, 2, v_v_2102_);
lean_ctor_set(v___x_2126_, 1, v_k_2101_);
lean_ctor_set(v___x_2126_, 0, v___x_2134_);
v___x_2136_ = v___x_2126_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_r_2120_);
lean_ctor_set(v_reuseFailAlloc_2140_, 4, v_r_2104_);
v___x_2136_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 4, v___x_2136_);
lean_ctor_set(v___x_2114_, 3, v___y_2132_);
lean_ctor_set(v___x_2114_, 2, v_v_2118_);
lean_ctor_set(v___x_2114_, 1, v_k_2117_);
lean_ctor_set(v___x_2114_, 0, v___x_2129_);
v___x_2138_ = v___x_2114_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2117_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2118_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v___y_2132_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
v___jp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_nat_add(v___x_2128_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec(v___x_2128_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_l_2119_);
lean_ctor_set(v___x_2093_, 0, v___x_2143_);
v___x_2145_ = v___x_2093_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_l_2090_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_l_2119_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_nat_add(v___x_2098_, v_size_2121_);
if (lean_obj_tag(v_r_2120_) == 0)
{
lean_object* v_size_2147_; 
v_size_2147_ = lean_ctor_get(v_r_2120_, 0);
lean_inc(v_size_2147_);
v___y_2131_ = v___x_2146_;
v___y_2132_ = v___x_2145_;
v___y_2133_ = v_size_2147_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_unsigned_to_nat(0u);
v___y_2131_ = v___x_2146_;
v___y_2132_ = v___x_2145_;
v___y_2133_ = v___x_2148_;
goto v___jp_2130_;
}
}
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_del_object(v___x_2093_);
v___x_2158_ = lean_nat_add(v___x_2098_, v_size_2099_);
v___x_2159_ = lean_nat_add(v___x_2158_, v_size_2100_);
lean_dec(v_size_2100_);
v___x_2160_ = lean_nat_add(v___x_2158_, v_size_2116_);
lean_dec(v___x_2158_);
lean_inc_ref(v_l_2090_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 4, v_l_2103_);
lean_ctor_set(v___x_2114_, 3, v_l_2090_);
lean_ctor_set(v___x_2114_, 2, v_v_2089_);
lean_ctor_set(v___x_2114_, 1, v_k_2088_);
lean_ctor_set(v___x_2114_, 0, v___x_2160_);
v___x_2162_ = v___x_2114_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_l_2090_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_l_2103_);
v___x_2162_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v_l_2090_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2170_ = lean_ctor_get(v_l_2090_, 4);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_l_2090_, 3);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_l_2090_, 2);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_l_2090_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_l_2090_, 0);
lean_dec(v_unused_2174_);
v___x_2164_ = v_l_2090_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v_l_2090_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v_r_2104_);
lean_ctor_set(v___x_2164_, 3, v___x_2162_);
lean_ctor_set(v___x_2164_, 2, v_v_2102_);
lean_ctor_set(v___x_2164_, 1, v_k_2101_);
lean_ctor_set(v___x_2164_, 0, v___x_2159_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_r_2104_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2182_; 
v_l_2182_ = lean_ctor_get(v_impl_2097_, 3);
lean_inc(v_l_2182_);
if (lean_obj_tag(v_l_2182_) == 0)
{
lean_object* v_r_2183_; lean_object* v_k_2184_; lean_object* v_v_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2208_; 
v_r_2183_ = lean_ctor_get(v_impl_2097_, 4);
v_k_2184_ = lean_ctor_get(v_impl_2097_, 1);
v_v_2185_ = lean_ctor_get(v_impl_2097_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_impl_2097_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2209_ = lean_ctor_get(v_impl_2097_, 3);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_impl_2097_, 0);
lean_dec(v_unused_2210_);
v___x_2187_ = v_impl_2097_;
v_isShared_2188_ = v_isSharedCheck_2208_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_r_2183_);
lean_inc(v_v_2185_);
lean_inc(v_k_2184_);
lean_dec(v_impl_2097_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2208_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2204_; 
v_k_2189_ = lean_ctor_get(v_l_2182_, 1);
v_v_2190_ = lean_ctor_get(v_l_2182_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_l_2182_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; 
v_unused_2205_ = lean_ctor_get(v_l_2182_, 4);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_l_2182_, 3);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_l_2182_, 0);
lean_dec(v_unused_2207_);
v___x_2192_ = v_l_2182_;
v_isShared_2193_ = v_isSharedCheck_2204_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
lean_dec(v_l_2182_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2204_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2183_, 2);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 4, v_r_2183_);
lean_ctor_set(v___x_2192_, 3, v_r_2183_);
lean_ctor_set(v___x_2192_, 2, v_v_2089_);
lean_ctor_set(v___x_2192_, 1, v_k_2088_);
lean_ctor_set(v___x_2192_, 0, v___x_2098_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_r_2183_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_r_2183_);
v___x_2196_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
lean_inc(v_r_2183_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 3, v_r_2183_);
lean_ctor_set(v___x_2187_, 0, v___x_2098_);
v___x_2198_ = v___x_2187_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2184_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2185_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_r_2183_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_r_2183_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v___x_2198_);
lean_ctor_set(v___x_2093_, 3, v___x_2196_);
lean_ctor_set(v___x_2093_, 2, v_v_2190_);
lean_ctor_set(v___x_2093_, 1, v_k_2189_);
lean_ctor_set(v___x_2093_, 0, v___x_2194_);
v___x_2200_ = v___x_2093_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2189_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2190_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v___x_2198_);
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
}
}
else
{
lean_object* v_r_2211_; 
v_r_2211_ = lean_ctor_get(v_impl_2097_, 4);
lean_inc(v_r_2211_);
if (lean_obj_tag(v_r_2211_) == 0)
{
lean_object* v_k_2212_; lean_object* v_v_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2224_; 
v_k_2212_ = lean_ctor_get(v_impl_2097_, 1);
v_v_2213_ = lean_ctor_get(v_impl_2097_, 2);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_impl_2097_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2225_ = lean_ctor_get(v_impl_2097_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_impl_2097_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_impl_2097_, 0);
lean_dec(v_unused_2227_);
v___x_2215_ = v_impl_2097_;
v_isShared_2216_ = v_isSharedCheck_2224_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_v_2213_);
lean_inc(v_k_2212_);
lean_dec(v_impl_2097_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2224_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = lean_unsigned_to_nat(3u);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 4, v_l_2182_);
lean_ctor_set(v___x_2215_, 2, v_v_2089_);
lean_ctor_set(v___x_2215_, 1, v_k_2088_);
lean_ctor_set(v___x_2215_, 0, v___x_2098_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2182_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_l_2182_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_r_2211_);
lean_ctor_set(v___x_2093_, 3, v___x_2219_);
lean_ctor_set(v___x_2093_, 2, v_v_2213_);
lean_ctor_set(v___x_2093_, 1, v_k_2212_);
lean_ctor_set(v___x_2093_, 0, v___x_2217_);
v___x_2221_ = v___x_2093_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_2212_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_2213_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_r_2211_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_unsigned_to_nat(2u);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_impl_2097_);
lean_ctor_set(v___x_2093_, 3, v_r_2211_);
lean_ctor_set(v___x_2093_, 0, v___x_2228_);
v___x_2230_ = v___x_2093_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_r_2211_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_impl_2097_);
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
lean_object* v___x_2233_; 
lean_dec(v_v_2089_);
lean_dec(v_k_2088_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 2, v_v_2085_);
lean_ctor_set(v___x_2093_, 1, v_k_2084_);
v___x_2233_ = v___x_2093_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_size_2087_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_l_2090_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_r_2091_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_impl_2235_; lean_object* v___x_2236_; 
lean_dec(v_size_2087_);
v_impl_2235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2084_, v_v_2085_, v_l_2090_);
v___x_2236_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2091_) == 0)
{
lean_object* v_size_2237_; lean_object* v_size_2238_; lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v_l_2241_; lean_object* v_r_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_size_2237_ = lean_ctor_get(v_r_2091_, 0);
v_size_2238_ = lean_ctor_get(v_impl_2235_, 0);
v_k_2239_ = lean_ctor_get(v_impl_2235_, 1);
v_v_2240_ = lean_ctor_get(v_impl_2235_, 2);
v_l_2241_ = lean_ctor_get(v_impl_2235_, 3);
v_r_2242_ = lean_ctor_get(v_impl_2235_, 4);
lean_inc(v_r_2242_);
v___x_2243_ = lean_unsigned_to_nat(3u);
v___x_2244_ = lean_nat_mul(v___x_2243_, v_size_2237_);
v___x_2245_ = lean_nat_dec_lt(v___x_2244_, v_size_2238_);
lean_dec(v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec(v_r_2242_);
v___x_2246_ = lean_nat_add(v___x_2236_, v_size_2238_);
v___x_2247_ = lean_nat_add(v___x_2246_, v_size_2237_);
lean_dec(v___x_2246_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 3, v_impl_2235_);
lean_ctor_set(v___x_2093_, 0, v___x_2247_);
v___x_2249_ = v___x_2093_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v_impl_2235_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v_r_2091_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2316_; 
lean_inc(v_l_2241_);
lean_inc(v_v_2240_);
lean_inc(v_k_2239_);
lean_inc(v_size_2238_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_impl_2235_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; 
v_unused_2317_ = lean_ctor_get(v_impl_2235_, 4);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_impl_2235_, 3);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_impl_2235_, 2);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_impl_2235_, 1);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_impl_2235_, 0);
lean_dec(v_unused_2321_);
v___x_2252_ = v_impl_2235_;
v_isShared_2253_ = v_isSharedCheck_2316_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v_impl_2235_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2316_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_size_2254_; lean_object* v_size_2255_; lean_object* v_k_2256_; lean_object* v_v_2257_; lean_object* v_l_2258_; lean_object* v_r_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_size_2254_ = lean_ctor_get(v_l_2241_, 0);
v_size_2255_ = lean_ctor_get(v_r_2242_, 0);
v_k_2256_ = lean_ctor_get(v_r_2242_, 1);
v_v_2257_ = lean_ctor_get(v_r_2242_, 2);
v_l_2258_ = lean_ctor_get(v_r_2242_, 3);
v_r_2259_ = lean_ctor_get(v_r_2242_, 4);
v___x_2260_ = lean_unsigned_to_nat(2u);
v___x_2261_ = lean_nat_mul(v___x_2260_, v_size_2254_);
v___x_2262_ = lean_nat_dec_lt(v_size_2255_, v___x_2261_);
lean_dec(v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2291_; 
lean_inc(v_r_2259_);
lean_inc(v_l_2258_);
lean_inc(v_v_2257_);
lean_inc(v_k_2256_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2292_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_r_2242_, 2);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_r_2242_, 1);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2296_);
v___x_2264_ = v_r_2242_;
v_isShared_2265_ = v_isSharedCheck_2291_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v_r_2242_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2291_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___x_2279_; lean_object* v___y_2281_; 
v___x_2266_ = lean_nat_add(v___x_2236_, v_size_2238_);
lean_dec(v_size_2238_);
v___x_2267_ = lean_nat_add(v___x_2266_, v_size_2237_);
lean_dec(v___x_2266_);
v___x_2279_ = lean_nat_add(v___x_2236_, v_size_2254_);
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_size_2289_; 
v_size_2289_ = lean_ctor_get(v_l_2258_, 0);
lean_inc(v_size_2289_);
v___y_2281_ = v_size_2289_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___y_2281_ = v___x_2290_;
goto v___jp_2280_;
}
v___jp_2268_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_nat_add(v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec(v___y_2270_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v_r_2091_);
lean_ctor_set(v___x_2264_, 3, v_r_2259_);
lean_ctor_set(v___x_2264_, 2, v_v_2089_);
lean_ctor_set(v___x_2264_, 1, v_k_2088_);
lean_ctor_set(v___x_2264_, 0, v___x_2272_);
v___x_2274_ = v___x_2264_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_r_2259_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v_r_2091_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 4, v___x_2274_);
lean_ctor_set(v___x_2252_, 3, v___y_2269_);
lean_ctor_set(v___x_2252_, 2, v_v_2257_);
lean_ctor_set(v___x_2252_, 1, v_k_2256_);
lean_ctor_set(v___x_2252_, 0, v___x_2267_);
v___x_2276_ = v___x_2252_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v___y_2269_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
v___jp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_nat_add(v___x_2279_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec(v___x_2279_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_l_2258_);
lean_ctor_set(v___x_2093_, 3, v_l_2241_);
lean_ctor_set(v___x_2093_, 2, v_v_2240_);
lean_ctor_set(v___x_2093_, 1, v_k_2239_);
lean_ctor_set(v___x_2093_, 0, v___x_2282_);
v___x_2284_ = v___x_2093_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_l_2258_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_nat_add(v___x_2236_, v_size_2237_);
if (lean_obj_tag(v_r_2259_) == 0)
{
lean_object* v_size_2286_; 
v_size_2286_ = lean_ctor_get(v_r_2259_, 0);
lean_inc(v_size_2286_);
v___y_2269_ = v___x_2284_;
v___y_2270_ = v___x_2285_;
v___y_2271_ = v_size_2286_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___y_2269_ = v___x_2284_;
v___y_2270_ = v___x_2285_;
v___y_2271_ = v___x_2287_;
goto v___jp_2268_;
}
}
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_del_object(v___x_2093_);
v___x_2297_ = lean_nat_add(v___x_2236_, v_size_2238_);
lean_dec(v_size_2238_);
v___x_2298_ = lean_nat_add(v___x_2297_, v_size_2237_);
lean_dec(v___x_2297_);
v___x_2299_ = lean_nat_add(v___x_2236_, v_size_2237_);
v___x_2300_ = lean_nat_add(v___x_2299_, v_size_2255_);
lean_dec(v___x_2299_);
lean_inc_ref(v_r_2091_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 4, v_r_2091_);
lean_ctor_set(v___x_2252_, 3, v_r_2242_);
lean_ctor_set(v___x_2252_, 2, v_v_2089_);
lean_ctor_set(v___x_2252_, 1, v_k_2088_);
lean_ctor_set(v___x_2252_, 0, v___x_2300_);
v___x_2302_ = v___x_2252_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_r_2242_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_r_2091_);
v___x_2302_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_isSharedCheck_2309_ = !lean_is_exclusive(v_r_2091_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2310_ = lean_ctor_get(v_r_2091_, 4);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_r_2091_, 3);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_r_2091_, 2);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_r_2091_, 1);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_2091_, 0);
lean_dec(v_unused_2314_);
v___x_2304_ = v_r_2091_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v_r_2091_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 4, v___x_2302_);
lean_ctor_set(v___x_2304_, 3, v_l_2241_);
lean_ctor_set(v___x_2304_, 2, v_v_2240_);
lean_ctor_set(v___x_2304_, 1, v_k_2239_);
lean_ctor_set(v___x_2304_, 0, v___x_2298_);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v___x_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2322_; 
v_l_2322_ = lean_ctor_get(v_impl_2235_, 3);
if (lean_obj_tag(v_l_2322_) == 0)
{
lean_object* v_r_2323_; lean_object* v_k_2324_; lean_object* v_v_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2336_; 
lean_inc_ref(v_l_2322_);
v_r_2323_ = lean_ctor_get(v_impl_2235_, 4);
v_k_2324_ = lean_ctor_get(v_impl_2235_, 1);
v_v_2325_ = lean_ctor_get(v_impl_2235_, 2);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_impl_2235_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; 
v_unused_2337_ = lean_ctor_get(v_impl_2235_, 3);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_impl_2235_, 0);
lean_dec(v_unused_2338_);
v___x_2327_ = v_impl_2235_;
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_r_2323_);
lean_inc(v_v_2325_);
lean_inc(v_k_2324_);
lean_dec(v_impl_2235_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2323_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 3, v_r_2323_);
lean_ctor_set(v___x_2327_, 2, v_v_2089_);
lean_ctor_set(v___x_2327_, 1, v_k_2088_);
lean_ctor_set(v___x_2327_, 0, v___x_2236_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_r_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_r_2323_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v___x_2331_);
lean_ctor_set(v___x_2093_, 3, v_l_2322_);
lean_ctor_set(v___x_2093_, 2, v_v_2325_);
lean_ctor_set(v___x_2093_, 1, v_k_2324_);
lean_ctor_set(v___x_2093_, 0, v___x_2329_);
v___x_2333_ = v___x_2093_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2324_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2325_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_l_2322_);
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
else
{
lean_object* v_r_2339_; 
v_r_2339_ = lean_ctor_get(v_impl_2235_, 4);
lean_inc(v_r_2339_);
if (lean_obj_tag(v_r_2339_) == 0)
{
lean_object* v_k_2340_; lean_object* v_v_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2364_; 
lean_inc(v_l_2322_);
v_k_2340_ = lean_ctor_get(v_impl_2235_, 1);
v_v_2341_ = lean_ctor_get(v_impl_2235_, 2);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_impl_2235_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; 
v_unused_2365_ = lean_ctor_get(v_impl_2235_, 4);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_impl_2235_, 3);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_impl_2235_, 0);
lean_dec(v_unused_2367_);
v___x_2343_ = v_impl_2235_;
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_v_2341_);
lean_inc(v_k_2340_);
lean_dec(v_impl_2235_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_k_2345_; lean_object* v_v_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2360_; 
v_k_2345_ = lean_ctor_get(v_r_2339_, 1);
v_v_2346_ = lean_ctor_get(v_r_2339_, 2);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_r_2339_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; 
v_unused_2361_ = lean_ctor_get(v_r_2339_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_r_2339_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2339_, 0);
lean_dec(v_unused_2363_);
v___x_2348_ = v_r_2339_;
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_v_2346_);
lean_inc(v_k_2345_);
lean_dec(v_r_2339_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_unsigned_to_nat(3u);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 4, v_l_2322_);
lean_ctor_set(v___x_2348_, 3, v_l_2322_);
lean_ctor_set(v___x_2348_, 2, v_v_2341_);
lean_ctor_set(v___x_2348_, 1, v_k_2340_);
lean_ctor_set(v___x_2348_, 0, v___x_2236_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2340_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2341_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_l_2322_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_l_2322_);
v___x_2352_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 4, v_l_2322_);
lean_ctor_set(v___x_2343_, 2, v_v_2089_);
lean_ctor_set(v___x_2343_, 1, v_k_2088_);
lean_ctor_set(v___x_2343_, 0, v___x_2236_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_l_2322_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_l_2322_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v___x_2354_);
lean_ctor_set(v___x_2093_, 3, v___x_2352_);
lean_ctor_set(v___x_2093_, 2, v_v_2346_);
lean_ctor_set(v___x_2093_, 1, v_k_2345_);
lean_ctor_set(v___x_2093_, 0, v___x_2350_);
v___x_2356_ = v___x_2093_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2345_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2346_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_unsigned_to_nat(2u);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_r_2339_);
lean_ctor_set(v___x_2093_, 3, v_impl_2235_);
lean_ctor_set(v___x_2093_, 0, v___x_2368_);
v___x_2370_ = v___x_2093_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_impl_2235_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_r_2339_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_k_2084_);
lean_ctor_set(v___x_2374_, 2, v_v_2085_);
lean_ctor_set(v___x_2374_, 3, v_t_2086_);
lean_ctor_set(v___x_2374_, 4, v_t_2086_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2375_, lean_object* v_v_2376_, lean_object* v_x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v_a_2386_; lean_object* v_optionsPerPos_2387_; lean_object* v_currNamespace_2388_; lean_object* v_openDecls_2389_; uint8_t v_inPattern_2390_; lean_object* v_subExpr_2391_; lean_object* v_depth_2392_; lean_object* v_lctxInitIndices_2393_; lean_object* v___y_2395_; lean_object* v___x_2400_; 
v___x_2385_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2378_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref(v___x_2385_);
v_optionsPerPos_2387_ = lean_ctor_get(v_a_2378_, 0);
v_currNamespace_2388_ = lean_ctor_get(v_a_2378_, 1);
v_openDecls_2389_ = lean_ctor_get(v_a_2378_, 2);
v_inPattern_2390_ = lean_ctor_get_uint8(v_a_2378_, sizeof(void*)*6);
v_subExpr_2391_ = lean_ctor_get(v_a_2378_, 3);
v_depth_2392_ = lean_ctor_get(v_a_2378_, 4);
v_lctxInitIndices_2393_ = lean_ctor_get(v_a_2378_, 5);
v___x_2400_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2387_, v_a_2386_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Options_empty;
v___y_2395_ = v___x_2401_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2402_; 
v_val_2402_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v___x_2400_, 1);
v___y_2395_ = v_val_2402_;
goto v___jp_2394_;
}
v___jp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2396_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2395_, v_k_2375_, v_v_2376_);
lean_inc(v_optionsPerPos_2387_);
v___x_2397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2386_, v___x_2396_, v_optionsPerPos_2387_);
lean_inc(v_lctxInitIndices_2393_);
lean_inc(v_depth_2392_);
lean_inc_ref(v_subExpr_2391_);
lean_inc(v_openDecls_2389_);
lean_inc(v_currNamespace_2388_);
v___x_2398_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_currNamespace_2388_);
lean_ctor_set(v___x_2398_, 2, v_openDecls_2389_);
lean_ctor_set(v___x_2398_, 3, v_subExpr_2391_);
lean_ctor_set(v___x_2398_, 4, v_depth_2392_);
lean_ctor_set(v___x_2398_, 5, v_lctxInitIndices_2393_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*6, v_inPattern_2390_);
lean_inc(v_a_2383_);
lean_inc_ref(v_a_2382_);
lean_inc(v_a_2381_);
lean_inc_ref(v_a_2380_);
lean_inc(v_a_2379_);
v___x_2399_ = lean_apply_7(v_x_2377_, v___x_2398_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, lean_box(0));
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2403_, lean_object* v_v_2404_, lean_object* v_x_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2403_, v_v_2404_, v_x_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2414_, lean_object* v_k_2415_, lean_object* v_v_2416_, lean_object* v_x_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2415_, v_v_2416_, v_x_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_k_2427_, lean_object* v_v_2428_, lean_object* v_x_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2426_, v_k_2427_, v_v_2428_, v_x_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2438_, lean_object* v_k_2439_, lean_object* v_v_2440_, lean_object* v_t_2441_, lean_object* v_hl_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2439_, v_v_2440_, v_t_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2444_, lean_object* v_stx_2445_){
_start:
{
uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = 0;
lean_inc(v_pos_2444_);
v___x_2447_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2447_, 0, v_pos_2444_);
lean_ctor_set(v___x_2447_, 1, v_pos_2444_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*2, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_setInfo(v___x_2447_, v_stx_2445_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v___x_2452_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2450_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2453_, v_stx_2449_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2462_, v_a_2463_);
lean_dec_ref(v_a_2463_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2466_, v_a_2467_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2486_, lean_object* v_e_2487_, uint8_t v_isBinder_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_lctx_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_lctx_2491_ = lean_ctor_get(v_a_2489_, 2);
v___x_2492_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v_stx_2486_);
v___x_2494_ = lean_box(0);
v___x_2495_ = 0;
lean_inc_ref(v_lctx_2491_);
v___x_2496_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2496_, 0, v___x_2493_);
lean_ctor_set(v___x_2496_, 1, v_lctx_2491_);
lean_ctor_set(v___x_2496_, 2, v___x_2494_);
lean_ctor_set(v___x_2496_, 3, v_e_2487_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*4, v_isBinder_2488_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*4 + 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2498_, lean_object* v_e_2499_, lean_object* v_isBinder_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
uint8_t v_isBinder_boxed_2503_; lean_object* v_res_2504_; 
v_isBinder_boxed_2503_ = lean_unbox(v_isBinder_2500_);
v_res_2504_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2498_, v_e_2499_, v_isBinder_boxed_2503_, v_a_2501_);
lean_dec_ref(v_a_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2505_, lean_object* v_e_2506_, uint8_t v_isBinder_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2505_, v_e_2506_, v_isBinder_2507_, v_a_2510_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2516_, lean_object* v_e_2517_, lean_object* v_isBinder_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
uint8_t v_isBinder_boxed_2526_; lean_object* v_res_2527_; 
v_isBinder_boxed_2526_ = lean_unbox(v_isBinder_2518_);
v_res_2527_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2516_, v_e_2517_, v_isBinder_boxed_2526_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2528_, lean_object* v_stx_2529_, lean_object* v_e_2530_, uint8_t v_isBinder_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2558_; 
v___x_2535_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2529_, v_e_2530_, v_isBinder_2531_, v_a_2533_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2558_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2558_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_steps_2542_; lean_object* v_infos_2543_; lean_object* v_holeIter_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2557_; 
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2536_);
v___x_2541_ = lean_st_ref_take(v_a_2532_);
v_steps_2542_ = lean_ctor_get(v___x_2541_, 0);
v_infos_2543_ = lean_ctor_get(v___x_2541_, 1);
v_holeIter_2544_ = lean_ctor_get(v___x_2541_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2546_ = v___x_2541_;
v_isShared_2547_ = v_isSharedCheck_2557_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_holeIter_2544_);
lean_inc(v_infos_2543_);
lean_inc(v_steps_2542_);
lean_dec(v___x_2541_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2557_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = lean_box(0);
v___x_2549_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2528_, v___x_2540_, v_infos_2543_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 1, v___x_2549_);
v___x_2551_ = v___x_2546_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_steps_2542_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_holeIter_2544_);
v___x_2551_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_st_ref_put(v_a_2532_, v___x_2551_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2548_);
v___x_2554_ = v___x_2538_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2548_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2559_, lean_object* v_stx_2560_, lean_object* v_e_2561_, lean_object* v_isBinder_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
uint8_t v_isBinder_boxed_2566_; lean_object* v_res_2567_; 
v_isBinder_boxed_2566_ = lean_unbox(v_isBinder_2562_);
v_res_2567_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2559_, v_stx_2560_, v_e_2561_, v_isBinder_boxed_2566_, v_a_2563_, v_a_2564_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2568_, lean_object* v_stx_2569_, lean_object* v_e_2570_, uint8_t v_isBinder_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2568_, v_stx_2569_, v_e_2570_, v_isBinder_2571_, v_a_2573_, v_a_2574_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2580_, lean_object* v_stx_2581_, lean_object* v_e_2582_, lean_object* v_isBinder_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
uint8_t v_isBinder_boxed_2591_; lean_object* v_res_2592_; 
v_isBinder_boxed_2591_ = lean_unbox(v_isBinder_2583_);
v_res_2592_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2580_, v_stx_2581_, v_e_2582_, v_isBinder_boxed_2591_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2593_, lean_object* v_fieldName_2594_, lean_object* v_stx_2595_, lean_object* v_val_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_lctx_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_lctx_2599_ = lean_ctor_get(v_a_2597_, 2);
lean_inc_ref(v_lctx_2599_);
v___x_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2600_, 0, v_projName_2593_);
lean_ctor_set(v___x_2600_, 1, v_fieldName_2594_);
lean_ctor_set(v___x_2600_, 2, v_lctx_2599_);
lean_ctor_set(v___x_2600_, 3, v_val_2596_);
lean_ctor_set(v___x_2600_, 4, v_stx_2595_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2602_, lean_object* v_fieldName_2603_, lean_object* v_stx_2604_, lean_object* v_val_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2602_, v_fieldName_2603_, v_stx_2604_, v_val_2605_, v_a_2606_);
lean_dec_ref(v_a_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2609_, lean_object* v_fieldName_2610_, lean_object* v_stx_2611_, lean_object* v_val_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2609_, v_fieldName_2610_, v_stx_2611_, v_val_2612_, v_a_2615_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2621_, lean_object* v_fieldName_2622_, lean_object* v_stx_2623_, lean_object* v_val_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2621_, v_fieldName_2622_, v_stx_2623_, v_val_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2633_, lean_object* v_projName_2634_, lean_object* v_fieldName_2635_, lean_object* v_stx_2636_, lean_object* v_val_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2664_; 
v___x_2641_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2634_, v_fieldName_2635_, v_stx_2636_, v_val_2637_, v_a_2639_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2664_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2664_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_steps_2648_; lean_object* v_infos_2649_; lean_object* v_holeIter_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2663_; 
v___x_2646_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2642_);
v___x_2647_ = lean_st_ref_take(v_a_2638_);
v_steps_2648_ = lean_ctor_get(v___x_2647_, 0);
v_infos_2649_ = lean_ctor_get(v___x_2647_, 1);
v_holeIter_2650_ = lean_ctor_get(v___x_2647_, 2);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2652_ = v___x_2647_;
v_isShared_2653_ = v_isSharedCheck_2663_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_holeIter_2650_);
lean_inc(v_infos_2649_);
lean_inc(v_steps_2648_);
lean_dec(v___x_2647_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2663_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2654_ = lean_box(0);
v___x_2655_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2633_, v___x_2646_, v_infos_2649_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v___x_2655_);
v___x_2657_ = v___x_2652_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_steps_2648_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_holeIter_2650_);
v___x_2657_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_st_ref_put(v_a_2638_, v___x_2657_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2654_);
v___x_2660_ = v___x_2644_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2654_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2665_, lean_object* v_projName_2666_, lean_object* v_fieldName_2667_, lean_object* v_stx_2668_, lean_object* v_val_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2665_, v_projName_2666_, v_fieldName_2667_, v_stx_2668_, v_val_2669_, v_a_2670_, v_a_2671_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2674_, lean_object* v_projName_2675_, lean_object* v_fieldName_2676_, lean_object* v_stx_2677_, lean_object* v_val_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2674_, v_projName_2675_, v_fieldName_2676_, v_stx_2677_, v_val_2678_, v_a_2680_, v_a_2681_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2687_, lean_object* v_projName_2688_, lean_object* v_fieldName_2689_, lean_object* v_stx_2690_, lean_object* v_val_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2687_, v_projName_2688_, v_fieldName_2689_, v_stx_2690_, v_val_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_val_2700_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2704_, v___y_2705_);
lean_dec_ref(v___y_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2708_, lean_object* v_stx_2709_, lean_object* v_e_2710_, uint8_t v_isBinder_2711_, lean_object* v_location_x3f_2712_, lean_object* v_docString_x3f_2713_, lean_object* v_mkDocString_x3f_2714_, uint8_t v_explicit_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2754_; 
v___x_2719_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2709_, v_e_2710_, v_isBinder_2711_, v_a_2717_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2754_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2754_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___y_2725_; 
if (lean_obj_tag(v_mkDocString_x3f_2714_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2713_) == 0)
{
v___y_2725_ = v_mkDocString_x3f_2714_;
goto v___jp_2724_;
}
else
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2753_; 
v_val_2745_ = lean_ctor_get(v_docString_x3f_2713_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_docString_x3f_2713_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2747_ = v_docString_x3f_2713_;
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v_docString_x3f_2713_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___f_2749_; lean_object* v___x_2751_; 
v___f_2749_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2749_, 0, v_val_2745_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___f_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___f_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
v___y_2725_ = v___x_2751_;
goto v___jp_2724_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2713_);
v___y_2725_ = v_mkDocString_x3f_2714_;
goto v___jp_2724_;
}
v___jp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_steps_2729_; lean_object* v_infos_2730_; lean_object* v_holeIter_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2744_; 
v___x_2726_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2726_, 0, v_a_2720_);
lean_ctor_set(v___x_2726_, 1, v_location_x3f_2712_);
lean_ctor_set(v___x_2726_, 2, v___y_2725_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*3, v_explicit_2715_);
v___x_2727_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
v___x_2728_ = lean_st_ref_take(v_a_2716_);
v_steps_2729_ = lean_ctor_get(v___x_2728_, 0);
v_infos_2730_ = lean_ctor_get(v___x_2728_, 1);
v_holeIter_2731_ = lean_ctor_get(v___x_2728_, 2);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2733_ = v___x_2728_;
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_holeIter_2731_);
lean_inc(v_infos_2730_);
lean_inc(v_steps_2729_);
lean_dec(v___x_2728_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2708_, v___x_2727_, v_infos_2730_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2736_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_steps_2729_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_holeIter_2731_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_st_ref_put(v_a_2716_, v___x_2738_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2735_);
v___x_2741_ = v___x_2722_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2735_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2755_, lean_object* v_stx_2756_, lean_object* v_e_2757_, lean_object* v_isBinder_2758_, lean_object* v_location_x3f_2759_, lean_object* v_docString_x3f_2760_, lean_object* v_mkDocString_x3f_2761_, lean_object* v_explicit_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v_isBinder_boxed_2766_; uint8_t v_explicit_boxed_2767_; lean_object* v_res_2768_; 
v_isBinder_boxed_2766_ = lean_unbox(v_isBinder_2758_);
v_explicit_boxed_2767_ = lean_unbox(v_explicit_2762_);
v_res_2768_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2755_, v_stx_2756_, v_e_2757_, v_isBinder_boxed_2766_, v_location_x3f_2759_, v_docString_x3f_2760_, v_mkDocString_x3f_2761_, v_explicit_boxed_2767_, v_a_2763_, v_a_2764_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2769_, lean_object* v_stx_2770_, lean_object* v_e_2771_, uint8_t v_isBinder_2772_, lean_object* v_location_x3f_2773_, lean_object* v_docString_x3f_2774_, lean_object* v_mkDocString_x3f_2775_, uint8_t v_explicit_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2769_, v_stx_2770_, v_e_2771_, v_isBinder_2772_, v_location_x3f_2773_, v_docString_x3f_2774_, v_mkDocString_x3f_2775_, v_explicit_2776_, v_a_2778_, v_a_2779_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2785_, lean_object* v_stx_2786_, lean_object* v_e_2787_, lean_object* v_isBinder_2788_, lean_object* v_location_x3f_2789_, lean_object* v_docString_x3f_2790_, lean_object* v_mkDocString_x3f_2791_, lean_object* v_explicit_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
uint8_t v_isBinder_boxed_2800_; uint8_t v_explicit_boxed_2801_; lean_object* v_res_2802_; 
v_isBinder_boxed_2800_ = lean_unbox(v_isBinder_2788_);
v_explicit_boxed_2801_ = lean_unbox(v_explicit_2792_);
v_res_2802_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2785_, v_stx_2786_, v_e_2787_, v_isBinder_boxed_2800_, v_location_x3f_2789_, v_docString_x3f_2790_, v_mkDocString_x3f_2791_, v_explicit_boxed_2801_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2803_, v_a_2804_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v_a_2813_; uint8_t v___x_2814_; lean_object* v___x_2815_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_n(v_a_2809_, 2);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2804_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v___x_2812_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2804_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = 0;
v___x_2815_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2811_, v_a_2809_, v_a_2813_, v___x_2814_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2823_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_a_2809_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2809_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_a_2809_);
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2815_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
return v___x_2808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2855_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2856_, lean_object* v_t_2857_){
_start:
{
if (lean_obj_tag(v_t_2857_) == 0)
{
lean_object* v_k_2858_; lean_object* v_l_2859_; lean_object* v_r_2860_; uint8_t v___x_2861_; 
v_k_2858_ = lean_ctor_get(v_t_2857_, 1);
v_l_2859_ = lean_ctor_get(v_t_2857_, 3);
v_r_2860_ = lean_ctor_get(v_t_2857_, 4);
v___x_2861_ = lean_nat_dec_lt(v_k_2856_, v_k_2858_);
if (v___x_2861_ == 0)
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_nat_dec_eq(v_k_2856_, v_k_2858_);
if (v___x_2862_ == 0)
{
v_t_2857_ = v_r_2860_;
goto _start;
}
else
{
return v___x_2862_;
}
}
else
{
v_t_2857_ = v_l_2859_;
goto _start;
}
}
else
{
uint8_t v___x_2865_; 
v___x_2865_ = 0;
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2866_, lean_object* v_t_2867_){
_start:
{
uint8_t v_res_2868_; lean_object* v_r_2869_; 
v_res_2868_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2866_, v_t_2867_);
lean_dec(v_t_2867_);
lean_dec(v_k_2866_);
v_r_2869_ = lean_box(v_res_2868_);
return v_r_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Syntax_getInfo_x3f(v_stx_2870_);
if (lean_obj_tag(v___x_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2894_; 
v_val_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2894_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_val_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2894_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_val_2876_) == 1)
{
uint8_t v_canonical_2880_; 
v_canonical_2880_ = lean_ctor_get_uint8(v_val_2876_, sizeof(void*)*2);
if (v_canonical_2880_ == 0)
{
lean_object* v_pos_2881_; lean_object* v_endPos_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v_pos_2881_ = lean_ctor_get(v_val_2876_, 0);
lean_inc(v_pos_2881_);
v_endPos_2882_ = lean_ctor_get(v_val_2876_, 1);
lean_inc(v_endPos_2882_);
lean_dec_ref_known(v_val_2876_, 2);
v___x_2883_ = lean_st_ref_get(v_a_2872_);
v___x_2884_ = lean_nat_dec_eq(v_pos_2881_, v_endPos_2882_);
lean_dec(v_endPos_2882_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v___x_2883_);
lean_dec(v_pos_2881_);
lean_del_object(v___x_2878_);
v___x_2885_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2885_;
}
else
{
lean_object* v_infos_2886_; uint8_t v___x_2887_; 
v_infos_2886_ = lean_ctor_get(v___x_2883_, 1);
lean_inc(v_infos_2886_);
lean_dec(v___x_2883_);
v___x_2887_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2881_, v_infos_2886_);
lean_dec(v_infos_2886_);
lean_dec(v_pos_2881_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_del_object(v___x_2878_);
v___x_2888_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2888_;
}
else
{
lean_object* v___x_2890_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 0);
lean_ctor_set(v___x_2878_, 0, v_stx_2870_);
v___x_2890_ = v___x_2878_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_stx_2870_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v___x_2892_; 
lean_dec_ref_known(v_val_2876_, 2);
lean_del_object(v___x_2878_);
v___x_2892_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2892_;
}
}
else
{
lean_object* v___x_2893_; 
lean_del_object(v___x_2878_);
lean_dec(v_val_2876_);
v___x_2893_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2893_;
}
}
}
else
{
lean_object* v___x_2895_; 
lean_dec(v___x_2875_);
v___x_2895_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
return v_res_2919_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2920_, lean_object* v_k_2921_, lean_object* v_t_2922_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2921_, v_t_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2924_, lean_object* v_k_2925_, lean_object* v_t_2926_){
_start:
{
uint8_t v_res_2927_; lean_object* v_r_2928_; 
v_res_2927_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2924_, v_k_2925_, v_t_2926_);
lean_dec(v_t_2926_);
lean_dec(v_k_2925_);
v_r_2928_ = lean_box(v_res_2927_);
return v_r_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___x_2937_; 
lean_inc(v_a_2935_);
lean_inc_ref(v_a_2934_);
lean_inc(v_a_2933_);
lean_inc_ref(v_a_2932_);
lean_inc(v_a_2931_);
lean_inc_ref(v_a_2930_);
v___x_2937_ = lean_apply_7(v_d_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, lean_box(0));
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2938_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2939_;
}
else
{
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2957_; 
lean_inc(v_a_2955_);
lean_inc_ref(v_a_2954_);
lean_inc(v_a_2953_);
lean_inc_ref(v_a_2952_);
lean_inc(v_a_2951_);
lean_inc_ref(v_a_2950_);
v___x_2957_ = lean_apply_7(v_d_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, lean_box(0));
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2958_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2959_;
}
else
{
return v___x_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
return v_res_2968_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2969_, lean_object* v_suggestion_x27_2970_, lean_object* v_x_2971_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 1)
{
lean_object* v_fvarId_2972_; lean_object* v___x_2973_; 
v_fvarId_2972_ = lean_ctor_get(v_x_2971_, 0);
lean_inc(v_fvarId_2972_);
lean_dec_ref_known(v_x_2971_, 1);
v___x_2973_ = lean_local_ctx_find(v_lctx_2969_, v_fvarId_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
uint8_t v___x_2974_; 
v___x_2974_ = 0;
return v___x_2974_;
}
else
{
lean_object* v_val_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_val_2975_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2976_ = l_Lean_LocalDecl_userName(v_val_2975_);
lean_dec(v_val_2975_);
v___x_2977_ = lean_name_eq(v___x_2976_, v_suggestion_x27_2970_);
lean_dec(v___x_2976_);
return v___x_2977_;
}
}
else
{
uint8_t v___x_2978_; 
lean_dec_ref(v_x_2971_);
lean_dec_ref(v_lctx_2969_);
v___x_2978_ = 0;
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2979_, lean_object* v_suggestion_x27_2980_, lean_object* v_x_2981_){
_start:
{
uint8_t v_res_2982_; lean_object* v_r_2983_; 
v_res_2982_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2979_, v_suggestion_x27_2980_, v_x_2981_);
lean_dec(v_suggestion_x27_2980_);
v_r_2983_ = lean_box(v_res_2982_);
return v_r_2983_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2984_, lean_object* v_lctx_2985_, lean_object* v_suggestion_x27_2986_){
_start:
{
lean_object* v___f_2987_; lean_object* v___x_2988_; 
v___f_2987_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2987_, 0, v_lctx_2985_);
lean_closure_set(v___f_2987_, 1, v_suggestion_x27_2986_);
v___x_2988_ = lean_find_expr(v___f_2987_, v_body_2984_);
lean_dec_ref(v___f_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
uint8_t v___x_2989_; 
v___x_2989_ = 0;
return v___x_2989_;
}
else
{
uint8_t v___x_2990_; 
lean_dec_ref_known(v___x_2988_, 1);
v___x_2990_ = 1;
return v___x_2990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2991_, lean_object* v_lctx_2992_, lean_object* v_suggestion_x27_2993_){
_start:
{
uint8_t v_res_2994_; lean_object* v_r_2995_; 
v_res_2994_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2991_, v_lctx_2992_, v_suggestion_x27_2993_);
lean_dec_ref(v_body_2991_);
v_r_2995_ = lean_box(v_res_2994_);
return v_r_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_toCold_3000_; lean_object* v_quotContext_3001_; lean_object* v_currMacroScope_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_toCold_3000_ = lean_ctor_get(v___y_2997_, 0);
lean_inc_ref(v_toCold_3000_);
lean_dec_ref(v___y_2997_);
v_quotContext_3001_ = lean_ctor_get(v_toCold_3000_, 8);
lean_inc(v_quotContext_3001_);
v_currMacroScope_3002_ = lean_ctor_get(v_toCold_3000_, 9);
lean_inc(v_currMacroScope_3002_);
lean_dec_ref(v_toCold_3000_);
v___x_3003_ = l_Lean_addMacroScope(v_quotContext_3001_, v_snd_2996_, v_currMacroScope_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_3014_, lean_object* v_body_3015_, uint8_t v_preserveName_3016_, lean_object* v_avoid_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; uint8_t v_fst_3057_; lean_object* v_snd_3058_; uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_Name_isAnonymous(v_suggestion_3014_);
if (v___x_3064_ == 0)
{
uint8_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = l_Lean_Name_hasMacroScopes(v_suggestion_3014_);
v___x_3066_ = l_Lean_Name_eraseMacroScopes(v_suggestion_3014_);
v_fst_3057_ = v___x_3065_;
v_snd_3058_ = v___x_3066_;
goto v___jp_3056_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3057_ = v___x_3064_;
v_snd_3058_ = v___x_3067_;
goto v___jp_3056_;
}
v___jp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = l_Lean_LocalContext_getUnusedName(v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
v___jp_3030_:
{
if (v_preserveName_3016_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v___y_3031_);
v___x_3034_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3035_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3034_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3046_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_unbox(v_a_3036_);
lean_dec(v_a_3036_);
if (v___x_3040_ == 0)
{
lean_del_object(v___x_3038_);
v___y_3026_ = v___y_3032_;
v___y_3027_ = v___y_3033_;
goto v___jp_3025_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_NameSet_contains(v_avoid_3017_, v___y_3033_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
lean_inc(v___y_3033_);
lean_inc_ref(v___y_3032_);
v___x_3042_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_3015_, v___y_3032_, v___y_3033_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3044_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___y_3033_);
v___x_3044_ = v___x_3038_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___y_3033_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_del_object(v___x_3038_);
v___y_3026_ = v___y_3032_;
v___y_3027_ = v___y_3033_;
goto v___jp_3025_;
}
}
else
{
lean_del_object(v___x_3038_);
v___y_3026_ = v___y_3032_;
v___y_3027_ = v___y_3033_;
goto v___jp_3025_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v___y_3033_);
v_a_3047_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3035_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3035_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v___x_3055_; 
lean_dec(v___y_3033_);
v___x_3055_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3031_, v_a_3022_, v_a_3023_);
return v___x_3055_;
}
}
v___jp_3056_:
{
lean_object* v_lctx_3059_; uint8_t v___x_3060_; 
v_lctx_3059_ = lean_ctor_get(v_a_3020_, 2);
v___x_3060_ = l_Lean_LocalContext_usesUserName(v_lctx_3059_, v_snd_3058_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_snd_3058_);
return v___x_3061_;
}
else
{
lean_object* v___f_3062_; 
lean_inc(v_snd_3058_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3062_, 0, v_snd_3058_);
if (v_preserveName_3016_ == 0)
{
v___y_3031_ = v___f_3062_;
v___y_3032_ = v_lctx_3059_;
v___y_3033_ = v_snd_3058_;
goto v___jp_3030_;
}
else
{
if (v_fst_3057_ == 0)
{
lean_object* v___x_3063_; 
lean_dec_ref(v___f_3062_);
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_snd_3058_);
return v___x_3063_;
}
else
{
v___y_3031_ = v___f_3062_;
v___y_3032_ = v_lctx_3059_;
v___y_3033_ = v_snd_3058_;
goto v___jp_3030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3068_, lean_object* v_body_3069_, lean_object* v_preserveName_3070_, lean_object* v_avoid_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
uint8_t v_preserveName_boxed_3079_; lean_object* v_res_3080_; 
v_preserveName_boxed_3079_ = lean_unbox(v_preserveName_3070_);
v_res_3080_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3068_, v_body_3069_, v_preserveName_boxed_3079_, v_avoid_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_avoid_3071_);
lean_dec_ref(v_body_3069_);
lean_dec(v_suggestion_3068_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v_holeIter_3084_; lean_object* v_curr_3085_; lean_object* v___x_3086_; lean_object* v_steps_3087_; lean_object* v_infos_3088_; lean_object* v_holeIter_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
v___x_3083_ = lean_st_ref_get(v___y_3081_);
v_holeIter_3084_ = lean_ctor_get(v___x_3083_, 2);
lean_inc_ref(v_holeIter_3084_);
lean_dec(v___x_3083_);
v_curr_3085_ = lean_ctor_get(v_holeIter_3084_, 0);
lean_inc(v_curr_3085_);
lean_dec_ref(v_holeIter_3084_);
v___x_3086_ = lean_st_ref_take(v___y_3081_);
v_steps_3087_ = lean_ctor_get(v___x_3086_, 0);
v_infos_3088_ = lean_ctor_get(v___x_3086_, 1);
v_holeIter_3089_ = lean_ctor_get(v___x_3086_, 2);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3091_ = v___x_3086_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_holeIter_3089_);
lean_inc(v_infos_3088_);
lean_inc(v_steps_3087_);
lean_dec(v___x_3086_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3089_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 2, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_steps_3087_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_infos_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_st_ref_put(v___y_3081_, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_curr_3085_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3100_);
lean_dec(v___y_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3104_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3119_, lean_object* v_e_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3128_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3122_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc_n(v_a_3129_, 2);
lean_dec_ref(v___x_3128_);
v___x_3130_ = l_Lean_mkIdent(v_n_3119_);
v___x_3131_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3129_, v___x_3130_);
v___x_3132_ = 0;
lean_inc(v___x_3131_);
v___x_3133_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3129_, v___x_3131_, v_e_3120_, v___x_3132_, v_a_3122_, v_a_3123_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3133_, 0);
lean_dec(v_unused_3141_);
v___x_3135_ = v___x_3133_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_dec(v___x_3133_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3131_);
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3131_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v___x_3131_);
v_a_3142_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3133_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3133_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3150_, lean_object* v_e_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3150_, v_e_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3160_, lean_object* v_x_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
lean_inc(v___y_3163_);
lean_inc_ref(v___y_3162_);
v___x_3169_ = lean_apply_8(v_d_3160_, v_x_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3170_, lean_object* v_x_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3170_, v_x_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
v___x_3189_ = lean_apply_8(v_k_3180_, v_b_3183_, v___y_3181_, v___y_3182_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, lean_box(0));
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v_b_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3190_, v___y_3191_, v___y_3192_, v_b_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3200_, uint8_t v_bi_3201_, lean_object* v_type_3202_, lean_object* v_k_3203_, uint8_t v_kind_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___f_3212_; lean_object* v___x_3213_; 
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
v___f_3212_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3212_, 0, v_k_3203_);
lean_closure_set(v___f_3212_, 1, v___y_3205_);
lean_closure_set(v___f_3212_, 2, v___y_3206_);
v___x_3213_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3200_, v_bi_3201_, v_type_3202_, v___f_3212_, v_kind_3204_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3213_) == 0)
{
return v___x_3213_;
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3222_, lean_object* v_bi_3223_, lean_object* v_type_3224_, lean_object* v_k_3225_, lean_object* v_kind_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
uint8_t v_bi_boxed_3234_; uint8_t v_kind_boxed_3235_; lean_object* v_res_3236_; 
v_bi_boxed_3234_ = lean_unbox(v_bi_3223_);
v_kind_boxed_3235_ = lean_unbox(v_kind_3226_);
v_res_3236_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3222_, v_bi_boxed_3234_, v_type_3224_, v_k_3225_, v_kind_boxed_3235_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3237_, lean_object* v_childIdx_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_subExpr_3247_; lean_object* v_optionsPerPos_3248_; lean_object* v_currNamespace_3249_; lean_object* v_openDecls_3250_; uint8_t v_inPattern_3251_; lean_object* v_depth_3252_; lean_object* v_lctxInitIndices_3253_; lean_object* v_pos_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_subExpr_3247_ = lean_ctor_get(v___y_3240_, 3);
v_optionsPerPos_3248_ = lean_ctor_get(v___y_3240_, 0);
v_currNamespace_3249_ = lean_ctor_get(v___y_3240_, 1);
v_openDecls_3250_ = lean_ctor_get(v___y_3240_, 2);
v_inPattern_3251_ = lean_ctor_get_uint8(v___y_3240_, sizeof(void*)*6);
v_depth_3252_ = lean_ctor_get(v___y_3240_, 4);
v_lctxInitIndices_3253_ = lean_ctor_get(v___y_3240_, 5);
v_pos_3254_ = lean_ctor_get(v_subExpr_3247_, 1);
v___x_3255_ = l_Lean_SubExpr_Pos_push(v_pos_3254_, v_childIdx_3238_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_child_3237_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
lean_inc(v_lctxInitIndices_3253_);
lean_inc(v_depth_3252_);
lean_inc(v_openDecls_3250_);
lean_inc(v_currNamespace_3249_);
lean_inc(v_optionsPerPos_3248_);
v___x_3257_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3257_, 0, v_optionsPerPos_3248_);
lean_ctor_set(v___x_3257_, 1, v_currNamespace_3249_);
lean_ctor_set(v___x_3257_, 2, v_openDecls_3250_);
lean_ctor_set(v___x_3257_, 3, v___x_3256_);
lean_ctor_set(v___x_3257_, 4, v_depth_3252_);
lean_ctor_set(v___x_3257_, 5, v_lctxInitIndices_3253_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*6, v_inPattern_3251_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
v___x_3258_ = lean_apply_7(v_x_3239_, v___x_3257_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, lean_box(0));
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3259_, lean_object* v_childIdx_3260_, lean_object* v_x_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3259_, v_childIdx_3260_, v_x_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3270_, lean_object* v_a_3271_, lean_object* v_x_3272_, lean_object* v_fvar_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
lean_inc_ref(v_fvar_3273_);
v___x_3281_ = lean_apply_8(v_v_3270_, v_fvar_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, lean_box(0));
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = l_Lean_Expr_bindingBody_x21(v_a_3271_);
v___x_3284_ = lean_expr_instantiate1(v___x_3283_, v_fvar_3273_);
lean_dec_ref(v_fvar_3273_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_apply_1(v_x_3272_, v_a_3282_);
v___x_3287_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3284_, v___x_3285_, v___x_3286_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
return v___x_3287_;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_fvar_3273_);
lean_dec_ref(v_x_3272_);
v_a_3288_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3281_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3281_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3296_, lean_object* v_a_3297_, lean_object* v_x_3298_, lean_object* v_fvar_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3296_, v_a_3297_, v_x_3298_, v_fvar_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v_a_3297_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3308_, lean_object* v_v_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v_a_3319_; lean_object* v___f_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3318_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3311_);
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc_n(v_a_3319_, 2);
lean_dec_ref(v___x_3318_);
v___f_3320_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3320_, 0, v_v_3309_);
lean_closure_set(v___f_3320_, 1, v_a_3319_);
lean_closure_set(v___f_3320_, 2, v_x_3310_);
v___x_3321_ = l_Lean_Expr_binderInfo(v_a_3319_);
v___x_3322_ = l_Lean_Expr_bindingDomain_x21(v_a_3319_);
lean_dec(v_a_3319_);
v___x_3323_ = 0;
v___x_3324_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3308_, v___x_3321_, v___x_3322_, v___f_3320_, v___x_3323_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3325_, lean_object* v_v_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3325_, v_v_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3336_, uint8_t v_preserveName_3337_, lean_object* v_avoid_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v___f_3346_; lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v_a_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___f_3346_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3346_, 0, v_d_3336_);
v___x_3347_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3339_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3339_);
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Lean_Expr_bindingName_x21(v_a_3348_);
lean_dec(v_a_3348_);
v___x_3352_ = l_Lean_Expr_bindingBody_x21(v_a_3350_);
lean_dec(v_a_3350_);
v___x_3353_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3351_, v___x_3352_, v_preserveName_3337_, v_avoid_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
lean_dec_ref(v___x_3352_);
lean_dec(v___x_3351_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_n(v_a_3354_, 2);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3355_, 0, v_a_3354_);
v___x_3356_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3354_, v___x_3355_, v___f_3346_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
return v___x_3356_;
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v___f_3346_);
v_a_3357_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3353_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3353_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3365_, lean_object* v_preserveName_3366_, lean_object* v_avoid_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
uint8_t v_preserveName_boxed_3375_; lean_object* v_res_3376_; 
v_preserveName_boxed_3375_ = lean_unbox(v_preserveName_3366_);
v_res_3376_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3365_, v_preserveName_boxed_3375_, v_avoid_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3377_, lean_object* v_d_3378_, uint8_t v_preserveName_3379_, lean_object* v_avoid_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3378_, v_preserveName_3379_, v_avoid_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3389_, lean_object* v_d_3390_, lean_object* v_preserveName_3391_, lean_object* v_avoid_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
uint8_t v_preserveName_boxed_3400_; lean_object* v_res_3401_; 
v_preserveName_boxed_3400_ = lean_unbox(v_preserveName_3391_);
v_res_3401_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3389_, v_d_3390_, v_preserveName_boxed_3400_, v_avoid_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_avoid_3392_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3402_, lean_object* v_child_3403_, lean_object* v_childIdx_3404_, lean_object* v_x_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3403_, v_childIdx_3404_, v_x_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_child_3415_, lean_object* v_childIdx_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3414_, v_child_3415_, v_childIdx_3416_, v_x_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3426_, lean_object* v_name_3427_, uint8_t v_bi_3428_, lean_object* v_type_3429_, lean_object* v_k_3430_, uint8_t v_kind_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3427_, v_bi_3428_, v_type_3429_, v_k_3430_, v_kind_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_name_3441_, lean_object* v_bi_3442_, lean_object* v_type_3443_, lean_object* v_k_3444_, lean_object* v_kind_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_bi_boxed_3453_; uint8_t v_kind_boxed_3454_; lean_object* v_res_3455_; 
v_bi_boxed_3453_ = lean_unbox(v_bi_3442_);
v_kind_boxed_3454_ = lean_unbox(v_kind_3445_);
v_res_3455_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3440_, v_name_3441_, v_bi_boxed_3453_, v_type_3443_, v_k_3444_, v_kind_boxed_3454_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3456_, lean_object* v_00_u03b2_3457_, lean_object* v_n_3458_, lean_object* v_v_3459_, lean_object* v_x_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3458_, v_v_3459_, v_x_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3469_, lean_object* v_00_u03b2_3470_, lean_object* v_n_3471_, lean_object* v_v_3472_, lean_object* v_x_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3469_, v_00_u03b2_3470_, v_n_3471_, v_v_3472_, v_x_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(lean_object* v_x_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_obj_tag_nat(v_x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl___boxed(lean_object* v_x_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(v_x_3484_);
lean_dec(v_x_3484_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3486_, lean_object* v_k_3487_){
_start:
{
if (lean_obj_tag(v_t_3486_) == 3)
{
lean_object* v_s_3488_; lean_object* v___x_3489_; 
v_s_3488_ = lean_ctor_get(v_t_3486_, 0);
lean_inc_ref(v_s_3488_);
lean_dec_ref_known(v_t_3486_, 1);
v___x_3489_ = lean_apply_1(v_k_3487_, v_s_3488_);
return v___x_3489_;
}
else
{
lean_dec(v_t_3486_);
return v_k_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3490_, lean_object* v_ctorIdx_3491_, lean_object* v_t_3492_, lean_object* v_h_3493_, lean_object* v_k_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3492_, v_k_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3496_, lean_object* v_ctorIdx_3497_, lean_object* v_t_3498_, lean_object* v_h_3499_, lean_object* v_k_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3496_, v_ctorIdx_3497_, v_t_3498_, v_h_3499_, v_k_3500_);
lean_dec(v_ctorIdx_3497_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3502_, lean_object* v_deep_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3502_, v_deep_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3505_, lean_object* v_t_3506_, lean_object* v_h_3507_, lean_object* v_deep_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3506_, v_deep_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3510_, lean_object* v_proof_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3510_, v_proof_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3513_, lean_object* v_t_3514_, lean_object* v_h_3515_, lean_object* v_proof_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3514_, v_proof_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3518_, lean_object* v_maxSteps_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3518_, v_maxSteps_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3521_, lean_object* v_t_3522_, lean_object* v_h_3523_, lean_object* v_maxSteps_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3522_, v_maxSteps_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3526_, lean_object* v_string_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3526_, v_string_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3529_, lean_object* v_t_3530_, lean_object* v_h_3531_, lean_object* v_string_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3530_, v_string_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3537_){
_start:
{
switch(lean_obj_tag(v_x_3537_))
{
case 0:
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3538_;
}
case 1:
{
lean_object* v___x_3539_; 
v___x_3539_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3539_;
}
case 2:
{
lean_object* v___x_3540_; 
v___x_3540_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3540_;
}
default: 
{
lean_object* v_s_3541_; 
v_s_3541_ = lean_ctor_get(v_x_3537_, 0);
lean_inc_ref(v_s_3541_);
return v_s_3541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3542_);
lean_dec(v_x_3542_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3544_, lean_object* v_stx_3545_, lean_object* v_e_3546_, lean_object* v_reason_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3551_ = 0;
v___x_3552_ = lean_box(0);
v___x_3553_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3547_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
v___x_3555_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3544_, v_stx_3545_, v_e_3546_, v___x_3551_, v___x_3552_, v___x_3554_, v___x_3552_, v___x_3551_, v_a_3548_, v_a_3549_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3556_, lean_object* v_stx_3557_, lean_object* v_e_3558_, lean_object* v_reason_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3556_, v_stx_3557_, v_e_3558_, v_reason_3559_, v_a_3560_, v_a_3561_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec(v_reason_3559_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3564_, lean_object* v_stx_3565_, lean_object* v_e_3566_, lean_object* v_reason_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3564_, v_stx_3565_, v_e_3566_, v_reason_3567_, v_a_3569_, v_a_3570_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3576_, lean_object* v_stx_3577_, lean_object* v_e_3578_, lean_object* v_reason_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3576_, v_stx_3577_, v_e_3578_, v_reason_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_reason_3579_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3588_, lean_object* v_ctx_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_optionsPerPos_3596_; lean_object* v_currNamespace_3597_; lean_object* v_openDecls_3598_; uint8_t v_inPattern_3599_; lean_object* v_subExpr_3600_; lean_object* v_depth_3601_; lean_object* v_lctxInitIndices_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_optionsPerPos_3596_ = lean_ctor_get(v_ctx_3589_, 0);
v_currNamespace_3597_ = lean_ctor_get(v_ctx_3589_, 1);
v_openDecls_3598_ = lean_ctor_get(v_ctx_3589_, 2);
v_inPattern_3599_ = lean_ctor_get_uint8(v_ctx_3589_, sizeof(void*)*6);
v_subExpr_3600_ = lean_ctor_get(v_ctx_3589_, 3);
v_depth_3601_ = lean_ctor_get(v_ctx_3589_, 4);
v_lctxInitIndices_3602_ = lean_ctor_get(v_ctx_3589_, 5);
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = lean_nat_add(v_depth_3601_, v___x_3603_);
lean_inc(v_lctxInitIndices_3602_);
lean_inc_ref(v_subExpr_3600_);
lean_inc(v_openDecls_3598_);
lean_inc(v_currNamespace_3597_);
lean_inc(v_optionsPerPos_3596_);
v___x_3605_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3605_, 0, v_optionsPerPos_3596_);
lean_ctor_set(v___x_3605_, 1, v_currNamespace_3597_);
lean_ctor_set(v___x_3605_, 2, v_openDecls_3598_);
lean_ctor_set(v___x_3605_, 3, v_subExpr_3600_);
lean_ctor_set(v___x_3605_, 4, v___x_3604_);
lean_ctor_set(v___x_3605_, 5, v_lctxInitIndices_3602_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*6, v_inPattern_3599_);
lean_inc(v_a_3594_);
lean_inc_ref(v_a_3593_);
lean_inc(v_a_3592_);
lean_inc_ref(v_a_3591_);
lean_inc(v_a_3590_);
v___x_3606_ = lean_apply_7(v_act_3588_, v___x_3605_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, lean_box(0));
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3607_, lean_object* v_ctx_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3607_, v_ctx_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_ctx_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3616_, lean_object* v_act_3617_, lean_object* v_ctx_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3617_, v_ctx_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3626_, lean_object* v_act_3627_, lean_object* v_ctx_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3626_, v_act_3627_, v_ctx_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_ctx_3628_);
return v_res_3635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3636_, lean_object* v_e_3637_){
_start:
{
lean_object* v___y_3639_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3643_ = lean_unsigned_to_nat(254u);
v___x_3644_ = lean_nat_dec_le(v___x_3643_, v_threshold_3636_);
if (v___x_3644_ == 0)
{
v___y_3639_ = v_threshold_3636_;
goto v___jp_3638_;
}
else
{
v___y_3639_ = v___x_3643_;
goto v___jp_3638_;
}
v___jp_3638_:
{
uint32_t v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3640_ = l_Lean_Expr_approxDepth(v_e_3637_);
v___x_3641_ = lean_uint32_to_nat(v___x_3640_);
v___x_3642_ = lean_nat_dec_le(v___x_3641_, v___y_3639_);
lean_dec(v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3645_, lean_object* v_e_3646_){
_start:
{
uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_res_3647_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3645_, v_e_3646_);
lean_dec_ref(v_e_3646_);
lean_dec(v_threshold_3645_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
uint8_t v___x_3659_; 
v___x_3659_ = l_Lean_Expr_isAtomic(v_e_3651_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3661_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3660_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3704_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3704_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3704_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_unbox(v_a_3662_);
if (v___x_3666_ == 0)
{
lean_object* v_depth_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_del_object(v___x_3664_);
v_depth_3667_ = lean_ctor_get(v_a_3652_, 4);
v___x_3668_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3669_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3668_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3691_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3691_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3691_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3674_ = lean_nat_sub(v_depth_3667_, v_a_3670_);
v___x_3675_ = lean_unsigned_to_nat(0u);
v___x_3676_ = lean_nat_dec_lt(v___x_3675_, v___x_3674_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3678_; 
lean_dec(v___x_3674_);
lean_dec(v_a_3670_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_a_3662_);
v___x_3678_ = v___x_3672_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3662_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v___x_3680_ = lean_unsigned_to_nat(2u);
v___x_3681_ = lean_nat_shiftr(v_a_3670_, v___x_3680_);
lean_dec(v_a_3670_);
v___x_3682_ = lean_nat_sub(v___x_3681_, v___x_3674_);
lean_dec(v___x_3674_);
lean_dec(v___x_3681_);
v___x_3683_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3682_, v_e_3651_);
lean_dec(v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_a_3662_);
v___x_3684_ = lean_box(v___x_3676_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3684_);
v___x_3686_ = v___x_3672_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
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
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_a_3662_);
v___x_3689_ = v___x_3672_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3662_);
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
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_a_3662_);
v_a_3692_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3669_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3669_);
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
else
{
lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_dec(v_a_3662_);
v___x_3700_ = lean_box(v___x_3659_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3700_);
v___x_3702_ = v___x_3664_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
return v___x_3661_;
}
}
else
{
uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = 0;
v___x_3706_ = lean_box(v___x_3705_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec_ref(v_e_3708_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Lean_Expr_isAtomic(v_e_3719_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3729_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3728_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3775_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3775_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3775_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_unbox(v_a_3730_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
lean_del_object(v___x_3732_);
lean_inc_ref(v_e_3719_);
v___x_3735_ = l_Lean_Meta_isProof(v_e_3719_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; uint8_t v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v___x_3737_ = lean_unbox(v_a_3736_);
if (v___x_3737_ == 0)
{
lean_dec(v_a_3730_);
lean_dec_ref(v_e_3719_);
return v___x_3735_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3738_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3739_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3738_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3751_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3740_, v_e_3719_);
lean_dec_ref(v_e_3719_);
lean_dec(v_a_3740_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3746_; 
lean_dec(v_a_3730_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v_a_3736_);
v___x_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3736_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
else
{
lean_object* v___x_3749_; 
lean_dec(v_a_3736_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v_a_3730_);
v___x_3749_ = v___x_3742_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3730_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3736_);
lean_dec(v_a_3730_);
lean_dec_ref(v_e_3719_);
v_a_3752_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3739_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3739_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
else
{
lean_object* v_a_3760_; uint8_t v___x_3761_; 
lean_dec_ref(v_e_3719_);
v_a_3760_ = lean_ctor_get(v___x_3735_, 0);
v___x_3761_ = l_Lean_Exception_isInterrupt(v_a_3760_);
if (v___x_3761_ == 0)
{
uint8_t v___x_3762_; 
lean_inc(v_a_3760_);
v___x_3762_ = l_Lean_Exception_isRuntime(v_a_3760_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3770_);
v___x_3764_ = v___x_3735_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3735_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set_tag(v___x_3764_, 0);
lean_ctor_set(v___x_3764_, 0, v_a_3730_);
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3730_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_dec(v_a_3730_);
return v___x_3735_;
}
}
else
{
lean_dec(v_a_3730_);
return v___x_3735_;
}
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_dec(v_a_3730_);
lean_dec_ref(v_e_3719_);
v___x_3771_ = lean_box(v___x_3727_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3771_);
v___x_3773_ = v___x_3732_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_dec_ref(v_e_3719_);
return v___x_3729_;
}
}
else
{
uint8_t v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec_ref(v_e_3719_);
v___x_3776_ = 0;
v___x_3777_ = lean_box(v___x_3776_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_ref_3802_; uint8_t v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_ref_3802_ = lean_ctor_get(v_a_3800_, 2);
v___x_3803_ = 0;
v___x_3804_ = l_Lean_SourceInfo_fromRef(v_ref_3802_, v___x_3803_);
v___x_3805_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3806_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3804_);
v___x_3807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3804_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = l_Lean_Syntax_node1(v___x_3804_, v___x_3805_, v___x_3807_);
v___x_3809_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3808_, v_a_3797_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; lean_object* v_a_3812_; lean_object* v___x_3813_; lean_object* v_a_3814_; lean_object* v___x_3815_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc_n(v_a_3810_, 2);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3797_);
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref(v___x_3811_);
v___x_3813_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3797_);
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref(v___x_3813_);
v___x_3815_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3812_, v_a_3810_, v_a_3814_, v_reason_3796_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v___x_3815_, 0);
lean_dec(v_unused_3823_);
v___x_3817_ = v___x_3815_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v___x_3815_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_a_3810_);
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3810_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3810_);
v_a_3824_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3815_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3815_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec_ref(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_reason_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3844_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec(v_a_3854_);
lean_dec_ref(v_a_3853_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_reason_3848_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
if (lean_obj_tag(v_x_3857_) == 0)
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3865_;
}
else
{
lean_object* v_head_3866_; lean_object* v_tail_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_head_3866_ = lean_ctor_get(v_x_3857_, 0);
lean_inc(v_head_3866_);
v_tail_3867_ = lean_ctor_get(v_x_3857_, 1);
lean_inc(v_tail_3867_);
lean_dec_ref_known(v_x_3857_, 2);
v___x_3868_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
v___x_3869_ = lean_apply_7(v_head_3866_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, lean_box(0));
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_dec(v_tail_3867_);
return v___x_3869_;
}
else
{
lean_object* v_a_3870_; uint8_t v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
v___x_3871_ = l_Lean_Exception_isInterrupt(v_a_3870_);
if (v___x_3871_ == 0)
{
uint8_t v___x_3872_; 
lean_inc(v_a_3870_);
v___x_3872_ = l_Lean_Exception_isRuntime(v_a_3870_);
if (v___x_3872_ == 0)
{
if (lean_obj_tag(v_a_3870_) == 0)
{
lean_dec_ref_known(v_a_3870_, 2);
lean_dec(v_tail_3867_);
return v___x_3869_;
}
else
{
lean_object* v_id_3873_; uint8_t v___x_3874_; 
v_id_3873_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_id_3873_);
lean_dec_ref_known(v_a_3870_, 2);
v___x_3874_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3868_, v_id_3873_);
lean_dec(v_id_3873_);
if (v___x_3874_ == 0)
{
lean_dec(v_tail_3867_);
return v___x_3869_;
}
else
{
lean_dec_ref_known(v___x_3869_, 1);
v_x_3857_ = v_tail_3867_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3870_);
lean_dec(v_tail_3867_);
return v___x_3869_;
}
}
else
{
lean_dec(v_a_3870_);
lean_dec(v_tail_3867_);
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_){
_start:
{
if (lean_obj_tag(v_x_3885_) == 0)
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v___y_3896_; lean_object* v_a_3897_; lean_object* v___x_3906_; lean_object* v_env_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3894_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3906_ = lean_st_ref_get(v_a_3891_);
v_env_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc_ref(v_env_3907_);
lean_dec(v___x_3906_);
v___x_3908_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3909_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3908_, v_env_3907_, v_x_3885_);
v___x_3910_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3909_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3911_, v_a_3886_, v_a_3887_, v_a_3888_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_dec(v_x_3885_);
return v___x_3912_;
}
else
{
lean_object* v_a_3913_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
v___y_3896_ = v___x_3912_;
v_a_3897_ = v_a_3913_;
goto v___jp_3895_;
}
}
else
{
lean_object* v_a_3914_; 
v_a_3914_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3914_);
v___y_3896_ = v___x_3910_;
v_a_3897_ = v_a_3914_;
goto v___jp_3895_;
}
v___jp_3895_:
{
uint8_t v___x_3898_; 
v___x_3898_ = l_Lean_Exception_isInterrupt(v_a_3897_);
if (v___x_3898_ == 0)
{
uint8_t v___x_3899_; 
lean_inc_ref(v_a_3897_);
v___x_3899_ = l_Lean_Exception_isRuntime(v_a_3897_);
if (v___x_3899_ == 0)
{
if (lean_obj_tag(v_a_3897_) == 0)
{
lean_dec_ref_known(v_a_3897_, 2);
lean_dec(v_x_3885_);
return v___y_3896_;
}
else
{
lean_object* v_id_3900_; uint8_t v___x_3901_; 
v_id_3900_ = lean_ctor_get(v_a_3897_, 0);
lean_inc(v_id_3900_);
lean_dec_ref_known(v_a_3897_, 2);
v___x_3901_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3894_, v_id_3900_);
lean_dec(v_id_3900_);
if (v___x_3901_ == 0)
{
lean_dec(v_x_3885_);
return v___y_3896_;
}
else
{
uint8_t v___x_3902_; 
lean_dec_ref(v___y_3896_);
v___x_3902_ = l_Lean_Name_isAtomic(v_x_3885_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_Name_getRoot(v_x_3885_);
lean_dec(v_x_3885_);
v_x_3885_ = v___x_3903_;
goto _start;
}
else
{
lean_object* v___x_3905_; 
lean_dec(v_x_3885_);
v___x_3905_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3905_;
}
}
}
}
else
{
lean_dec_ref(v_a_3897_);
lean_dec(v_x_3885_);
return v___y_3896_;
}
}
else
{
lean_dec_ref(v_a_3897_);
lean_dec(v_x_3885_);
return v___y_3896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v_env_3931_; uint8_t v___x_3932_; lean_object* v_env_3933_; lean_object* v___x_3934_; lean_object* v_toCold_3935_; lean_object* v_mctx_3936_; lean_object* v_lctx_3937_; lean_object* v_options_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3930_ = lean_st_ref_get(v___y_3928_);
v_env_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc_ref(v_env_3931_);
lean_dec(v___x_3930_);
v___x_3932_ = 0;
v_env_3933_ = l_Lean_Environment_setRecordingDeps(v_env_3931_, v___x_3932_);
v___x_3934_ = lean_st_ref_get(v___y_3926_);
v_toCold_3935_ = lean_ctor_get(v___y_3927_, 0);
v_mctx_3936_ = lean_ctor_get(v___x_3934_, 0);
lean_inc_ref(v_mctx_3936_);
lean_dec(v___x_3934_);
v_lctx_3937_ = lean_ctor_get(v___y_3925_, 2);
v_options_3938_ = lean_ctor_get(v_toCold_3935_, 2);
lean_inc_ref(v_options_3938_);
lean_inc_ref(v_lctx_3937_);
v___x_3939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3939_, 0, v_env_3933_);
lean_ctor_set(v___x_3939_, 1, v_mctx_3936_);
lean_ctor_set(v___x_3939_, 2, v_lctx_3937_);
lean_ctor_set(v___x_3939_, 3, v_options_3938_);
v___x_3940_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
lean_ctor_set(v___x_3940_, 1, v_msgData_3924_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_ref_3955_; lean_object* v___x_3956_; lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3965_; 
v_ref_3955_ = lean_ctor_get(v___y_3952_, 2);
v___x_3956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
lean_inc(v_ref_3955_);
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v_ref_3955_);
lean_ctor_set(v___x_3961_, 1, v_a_3957_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 1);
lean_ctor_set(v___x_3959_, 0, v___x_3961_);
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
return v_res_3972_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3975_ = l_Lean_stringToMessageData(v___x_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_3976_);
v___x_3985_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_dec(v_a_3976_);
return v___x_3985_;
}
else
{
lean_object* v_a_3986_; uint8_t v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
v___x_3987_ = l_Lean_Exception_isInterrupt(v_a_3986_);
if (v___x_3987_ == 0)
{
uint8_t v___x_3988_; 
lean_inc(v_a_3986_);
v___x_3988_ = l_Lean_Exception_isRuntime(v_a_3986_);
if (v___x_3988_ == 0)
{
if (lean_obj_tag(v_a_3986_) == 0)
{
lean_dec_ref_known(v_a_3986_, 2);
lean_dec(v_a_3976_);
return v___x_3985_;
}
else
{
lean_object* v_id_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4002_; 
v_id_3989_ = lean_ctor_get(v_a_3986_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_a_3986_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v_a_3986_, 1);
lean_dec(v_unused_4003_);
v___x_3991_ = v_a_3986_;
v_isShared_3992_ = v_isSharedCheck_4002_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_id_3989_);
lean_dec(v_a_3986_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4002_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
uint8_t v___x_3993_; 
v___x_3993_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3984_, v_id_3989_);
lean_dec(v_id_3989_);
if (v___x_3993_ == 0)
{
lean_del_object(v___x_3991_);
lean_dec(v_a_3976_);
return v___x_3985_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec_ref_known(v___x_3985_, 1);
v___x_3994_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_3995_ = l_Lean_MessageData_ofName(v_a_3976_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set_tag(v___x_3991_, 7);
lean_ctor_set(v___x_3991_, 1, v___x_3995_);
lean_ctor_set(v___x_3991_, 0, v___x_3994_);
v___x_3997_ = v___x_3991_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_3999_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_4000_;
}
}
}
}
}
else
{
lean_dec(v_a_3986_);
lean_dec(v_a_3976_);
return v___x_3985_;
}
}
else
{
lean_dec(v_a_3986_);
lean_dec(v_a_3976_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v_a_4022_; lean_object* v___x_4023_; 
v___x_4021_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4014_);
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4021_);
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4016_);
v___x_4023_ = lean_infer_type(v_a_4022_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4026_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4024_, v___x_4025_, v_x_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
return v___x_4026_;
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v_x_4013_);
v_a_4027_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4023_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4023_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
return v_res_4043_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4064_ = l_String_toRawSubstring_x27(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec_ref(v_a_4109_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4121_ = l_Lean_Core_checkSystem(v___x_4120_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec_ref_known(v___x_4121_, 1);
v___x_4122_ = lean_st_ref_get(v_a_4114_);
v___x_4123_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4124_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4123_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v_steps_4126_; uint8_t v___x_4127_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v_steps_4126_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_steps_4126_);
lean_dec(v___x_4122_);
v___x_4127_ = lean_nat_dec_le(v_a_4125_, v_steps_4126_);
lean_dec(v_steps_4126_);
lean_dec(v_a_4125_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; lean_object* v_steps_4129_; lean_object* v_infos_4130_; lean_object* v_holeIter_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4310_; 
v___x_4128_ = lean_st_ref_take(v_a_4114_);
v_steps_4129_ = lean_ctor_get(v___x_4128_, 0);
v_infos_4130_ = lean_ctor_get(v___x_4128_, 1);
v_holeIter_4131_ = lean_ctor_get(v___x_4128_, 2);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4133_ = v___x_4128_;
v_isShared_4134_ = v_isSharedCheck_4310_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_holeIter_4131_);
lean_inc(v_infos_4130_);
lean_inc(v_steps_4129_);
lean_dec(v___x_4128_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4310_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4135_ = lean_unsigned_to_nat(1u);
v___x_4136_ = lean_nat_add(v_steps_4129_, v___x_4135_);
lean_dec(v_steps_4129_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4136_);
v___x_4138_ = v___x_4133_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4309_, 1, v_infos_4130_);
lean_ctor_set(v_reuseFailAlloc_4309_, 2, v_holeIter_4131_);
v___x_4138_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_st_ref_put(v_a_4114_, v___x_4138_);
v___x_4140_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4113_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4141_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; uint8_t v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = lean_unbox(v_a_4143_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; 
lean_inc(v_a_4141_);
v___x_4145_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4141_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; uint8_t v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v___x_4147_ = lean_unbox(v_a_4146_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_dec(v_a_4143_);
v___x_4148_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___f_4150_; lean_object* v___x_4151_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___f_4150_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4150_, 0, v_a_4149_);
v___x_4151_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4150_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__1));
v___x_4154_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4153_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4215_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4215_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4215_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_unbox(v_a_4155_);
lean_dec(v_a_4155_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4161_; 
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v_a_4152_);
v___x_4161_ = v___x_4157_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4152_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_del_object(v___x_4157_);
v___x_4163_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4164_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4163_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4206_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4206_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4206_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
uint8_t v___x_4169_; 
v___x_4169_ = lean_unbox(v_a_4165_);
lean_dec(v_a_4165_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4171_; 
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v_a_4152_);
v___x_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4152_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
else
{
uint8_t v___x_4173_; 
v___x_4173_ = l_Lean_Expr_isMData(v_a_4141_);
lean_dec(v_a_4141_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_del_object(v___x_4167_);
v___x_4174_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4175_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4174_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_toCold_4176_; lean_object* v_a_4177_; lean_object* v_ref_4178_; lean_object* v_quotContext_4179_; lean_object* v_currMacroScope_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_toCold_4176_ = lean_ctor_get(v_a_4117_, 0);
v_a_4177_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4175_, 1);
v_ref_4178_ = lean_ctor_get(v_a_4117_, 2);
v_quotContext_4179_ = lean_ctor_get(v_toCold_4176_, 8);
v_currMacroScope_4180_ = lean_ctor_get(v_toCold_4176_, 9);
v___x_4181_ = lean_unbox(v_a_4146_);
lean_dec(v_a_4146_);
v___x_4182_ = l_Lean_SourceInfo_fromRef(v_ref_4178_, v___x_4181_);
v___x_4183_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4184_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__6));
v___x_4185_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
lean_inc_n(v___x_4182_, 7);
v___x_4186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4182_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__9));
v___x_4188_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__10, &l_Lean_PrettyPrinter_Delaborator_delab___closed__10_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10);
v___x_4189_ = lean_box(0);
lean_inc(v_currMacroScope_4180_);
lean_inc(v_quotContext_4179_);
v___x_4190_ = l_Lean_addMacroScope(v_quotContext_4179_, v___x_4189_, v_currMacroScope_4180_);
v___x_4191_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4182_);
lean_ctor_set(v___x_4192_, 1, v___x_4188_);
lean_ctor_set(v___x_4192_, 2, v___x_4190_);
lean_ctor_set(v___x_4192_, 3, v___x_4191_);
v___x_4193_ = l_Lean_Syntax_node1(v___x_4182_, v___x_4187_, v___x_4192_);
v___x_4194_ = l_Lean_Syntax_node2(v___x_4182_, v___x_4184_, v___x_4186_, v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4182_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4198_ = l_Lean_Syntax_node1(v___x_4182_, v___x_4197_, v_a_4177_);
v___x_4199_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4182_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = l_Lean_Syntax_node5(v___x_4182_, v___x_4183_, v___x_4194_, v_a_4152_, v___x_4196_, v___x_4198_, v___x_4200_);
v___x_4202_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4201_, v_a_4113_);
return v___x_4202_;
}
else
{
lean_dec(v_a_4152_);
lean_dec(v_a_4146_);
return v___x_4175_;
}
}
else
{
lean_object* v___x_4204_; 
lean_dec(v_a_4146_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v_a_4152_);
v___x_4204_ = v___x_4167_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4152_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
v_a_4207_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4164_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4164_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
v_a_4216_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4154_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4154_);
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
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
return v___x_4151_;
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
v_a_4224_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4148_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4148_);
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
lean_dec(v_a_4146_);
lean_dec(v_a_4141_);
v___x_4232_ = lean_box(1);
v___x_4233_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4232_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4117_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4236_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4235_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4274_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4274_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4274_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
uint8_t v___x_4241_; 
v___x_4241_ = lean_unbox(v_a_4237_);
lean_dec(v_a_4237_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4243_; 
lean_dec(v_a_4143_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v_a_4234_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4234_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
else
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_del_object(v___x_4239_);
v___x_4245_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4246_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4245_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_toCold_4247_; lean_object* v_a_4248_; lean_object* v_ref_4249_; lean_object* v_quotContext_4250_; lean_object* v_currMacroScope_4251_; uint8_t v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_toCold_4247_ = lean_ctor_get(v_a_4117_, 0);
v_a_4248_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4246_, 1);
v_ref_4249_ = lean_ctor_get(v_a_4117_, 2);
v_quotContext_4250_ = lean_ctor_get(v_toCold_4247_, 8);
v_currMacroScope_4251_ = lean_ctor_get(v_toCold_4247_, 9);
v___x_4252_ = lean_unbox(v_a_4143_);
lean_dec(v_a_4143_);
v___x_4253_ = l_Lean_SourceInfo_fromRef(v_ref_4249_, v___x_4252_);
v___x_4254_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4255_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__6));
v___x_4256_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
lean_inc_n(v___x_4253_, 7);
v___x_4257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4253_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__9));
v___x_4259_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__10, &l_Lean_PrettyPrinter_Delaborator_delab___closed__10_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10);
v___x_4260_ = lean_box(0);
lean_inc(v_currMacroScope_4251_);
lean_inc(v_quotContext_4250_);
v___x_4261_ = l_Lean_addMacroScope(v_quotContext_4250_, v___x_4260_, v_currMacroScope_4251_);
v___x_4262_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4263_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4253_);
lean_ctor_set(v___x_4263_, 1, v___x_4259_);
lean_ctor_set(v___x_4263_, 2, v___x_4261_);
lean_ctor_set(v___x_4263_, 3, v___x_4262_);
v___x_4264_ = l_Lean_Syntax_node1(v___x_4253_, v___x_4258_, v___x_4263_);
v___x_4265_ = l_Lean_Syntax_node2(v___x_4253_, v___x_4255_, v___x_4257_, v___x_4264_);
v___x_4266_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4253_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4269_ = l_Lean_Syntax_node1(v___x_4253_, v___x_4268_, v_a_4248_);
v___x_4270_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4253_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_Syntax_node5(v___x_4253_, v___x_4254_, v___x_4265_, v_a_4234_, v___x_4267_, v___x_4269_, v___x_4271_);
v___x_4273_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4272_, v_a_4113_);
return v___x_4273_;
}
else
{
lean_dec(v_a_4234_);
lean_dec(v_a_4143_);
return v___x_4246_;
}
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_a_4234_);
lean_dec(v_a_4143_);
v_a_4275_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4236_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4236_);
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
lean_dec(v_a_4143_);
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_a_4143_);
lean_dec(v_a_4141_);
v_a_4283_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4145_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4145_);
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
else
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
lean_dec(v_a_4143_);
lean_dec(v_a_4141_);
v___x_4291_ = lean_box(0);
v___x_4292_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4291_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4117_);
return v___x_4292_;
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_a_4141_);
v_a_4293_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4142_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4142_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
v_a_4301_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4140_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4140_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = lean_box(2);
v___x_4312_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4311_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4117_);
return v___x_4312_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v___x_4122_);
v_a_4313_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4124_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4124_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_a_4321_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4121_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4121_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4329_, lean_object* v_msg_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4337_, lean_object* v_msg_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4337_, v_msg_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4345_, lean_object* v_x_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4355_, lean_object* v_x_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4355_, v_x_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4366_, lean_object* v_prec_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4376_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4375_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4389_; 
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4379_ = v___x_4376_;
v_isShared_4380_ = v_isSharedCheck_4389_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4376_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4389_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v_mctx_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4381_ = lean_st_ref_get(v_a_4371_);
v_mctx_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref(v_mctx_4382_);
lean_dec(v___x_4381_);
v___x_4383_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4383_, 0, v_mctx_4382_);
v___x_4384_ = lean_unbox(v_a_4377_);
lean_dec(v_a_4377_);
v___x_4385_ = l_Lean_Level_quote(v_l_4366_, v_prec_4367_, v___x_4384_, v___x_4383_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4385_);
v___x_4387_ = v___x_4379_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_l_4366_);
v_a_4390_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4376_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4376_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4398_, lean_object* v_prec_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4398_, v_prec_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_prec_4399_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4408_, lean_object* v_stx_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4409_, v___y_4410_, v___y_4411_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = lean_box(0);
v___x_4416_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4414_, v___x_4415_, v___y_4410_, v___y_4411_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; uint8_t v___x_4418_; lean_object* v___x_4419_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc_n(v_a_4417_, 2);
lean_dec_ref_known(v___x_4416_, 1);
v___x_4418_ = 0;
v___x_4419_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_a_4417_, v___x_4418_, v___y_4410_, v___y_4411_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4419_, 0);
lean_dec(v_unused_4427_);
v___x_4421_ = v___x_4419_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_dec(v___x_4419_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v_a_4417_);
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4417_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec(v_a_4417_);
v_a_4428_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4419_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4419_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
return v___x_4416_;
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
v_a_4436_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4413_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4413_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4444_, lean_object* v_stx_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v_x_410__boxed_4449_; lean_object* v_res_4450_; 
v_x_410__boxed_4449_ = lean_unbox(v_x_4444_);
v_res_4450_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_410__boxed_4449_, v_stx_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4476_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4477_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4475_, v___x_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4483_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4484_ = l_Lean_addBuiltinDocString(v___x_4482_, v___x_4483_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4514_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4515_ = l_Lean_addBuiltinDeclarationRanges(v___x_4513_, v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; lean_object* v_mctx_4522_; lean_object* v___x_4523_; lean_object* v_fst_4524_; lean_object* v_snd_4525_; lean_object* v___x_4526_; lean_object* v_cache_4527_; lean_object* v_zetaDeltaFVarIds_4528_; lean_object* v_postponed_4529_; lean_object* v_diag_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4539_; 
v___x_4521_ = lean_st_ref_get(v___y_4519_);
v_mctx_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc_ref(v_mctx_4522_);
lean_dec(v___x_4521_);
v___x_4523_ = lean_instantiate_level_mvars(v_mctx_4522_, v_l_4518_);
v_fst_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_fst_4524_);
v_snd_4525_ = lean_ctor_get(v___x_4523_, 1);
lean_inc(v_snd_4525_);
lean_dec_ref(v___x_4523_);
v___x_4526_ = lean_st_ref_take(v___y_4519_);
v_cache_4527_ = lean_ctor_get(v___x_4526_, 1);
v_zetaDeltaFVarIds_4528_ = lean_ctor_get(v___x_4526_, 2);
v_postponed_4529_ = lean_ctor_get(v___x_4526_, 3);
v_diag_4530_ = lean_ctor_get(v___x_4526_, 4);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; 
v_unused_4540_ = lean_ctor_get(v___x_4526_, 0);
lean_dec(v_unused_4540_);
v___x_4532_ = v___x_4526_;
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_diag_4530_);
lean_inc(v_postponed_4529_);
lean_inc(v_zetaDeltaFVarIds_4528_);
lean_inc(v_cache_4527_);
lean_dec(v___x_4526_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v_fst_4524_);
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_fst_4524_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_cache_4527_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_zetaDeltaFVarIds_4528_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_postponed_4529_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_diag_4530_);
v___x_4535_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_st_ref_put(v___y_4519_, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_snd_4525_);
return v___x_4537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4541_, v___y_4542_);
lean_dec(v___y_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4545_, v___y_4547_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4559_, lean_object* v_prec_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_l_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4563_);
v___x_4578_ = l_Lean_getPPInstantiateMVars(v___x_4577_);
lean_dec_ref(v___x_4577_);
if (v___x_4578_ == 0)
{
v_l_4567_ = v_l_4559_;
v___y_4568_ = v_a_4562_;
v___y_4569_ = v_a_4563_;
goto v___jp_4566_;
}
else
{
lean_object* v___x_4579_; lean_object* v_a_4580_; 
v___x_4579_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4559_, v_a_4562_);
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref(v___x_4579_);
v_l_4567_ = v_a_4580_;
v___y_4568_ = v_a_4562_;
v___y_4569_ = v_a_4563_;
goto v___jp_4566_;
}
v___jp_4566_:
{
lean_object* v___x_4570_; uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v_mctx_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4570_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4569_);
v___x_4571_ = l_Lean_getPPMVarsLevels(v___x_4570_);
lean_dec_ref(v___x_4570_);
v___x_4572_ = lean_st_ref_get(v___y_4568_);
v_mctx_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc_ref(v_mctx_4573_);
lean_dec(v___x_4572_);
v___x_4574_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4574_, 0, v_mctx_4573_);
v___x_4575_ = l_Lean_Level_quote(v_l_4567_, v_prec_4560_, v___x_4571_, v___x_4574_);
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
return v___x_4576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4581_, lean_object* v_prec_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_PrettyPrinter_delabLevel(v_l_4581_, v_prec_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_prec_4582_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___f_4596_; lean_object* v___x_8167__overap_4597_; lean_object* v___x_4598_; 
v___f_4596_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8167__overap_4597_ = lean_panic_fn_borrowed(v___f_4596_, v_msg_4590_);
lean_inc(v___y_4594_);
lean_inc_ref(v___y_4593_);
lean_inc(v___y_4592_);
lean_inc_ref(v___y_4591_);
v___x_4598_ = lean_apply_5(v___x_8167__overap_4597_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, lean_box(0));
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4606_, lean_object* v_msg_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4614_, lean_object* v_msg_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4614_, v_msg_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4622_, lean_object* v_opt_4623_){
_start:
{
lean_object* v_name_4624_; lean_object* v_defValue_4625_; lean_object* v_map_4626_; lean_object* v___x_4627_; 
v_name_4624_ = lean_ctor_get(v_opt_4623_, 0);
v_defValue_4625_ = lean_ctor_get(v_opt_4623_, 1);
v_map_4626_ = lean_ctor_get(v_opts_4622_, 0);
v___x_4627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4626_, v_name_4624_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_inc(v_defValue_4625_);
return v_defValue_4625_;
}
else
{
lean_object* v_val_4628_; 
v_val_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_val_4628_);
lean_dec_ref_known(v___x_4627_, 1);
if (lean_obj_tag(v_val_4628_) == 3)
{
lean_object* v_v_4629_; 
v_v_4629_ = lean_ctor_get(v_val_4628_, 0);
lean_inc(v_v_4629_);
lean_dec_ref_known(v_val_4628_, 1);
return v_v_4629_;
}
else
{
lean_dec(v_val_4628_);
lean_inc(v_defValue_4625_);
return v_defValue_4625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4630_, lean_object* v_opt_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4630_, v_opt_4631_);
lean_dec_ref(v_opt_4631_);
lean_dec_ref(v_opts_4630_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(lean_object* v_e_4633_, lean_object* v___y_4634_){
_start:
{
uint8_t v___x_4636_; 
v___x_4636_ = l_Lean_Expr_hasMVar(v_e_4633_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_e_4633_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; lean_object* v_mctx_4639_; lean_object* v___x_4640_; lean_object* v_fst_4641_; lean_object* v_snd_4642_; lean_object* v___x_4643_; lean_object* v_cache_4644_; lean_object* v_zetaDeltaFVarIds_4645_; lean_object* v_postponed_4646_; lean_object* v_diag_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4656_; 
v___x_4638_ = lean_st_ref_get(v___y_4634_);
v_mctx_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc_ref(v_mctx_4639_);
lean_dec(v___x_4638_);
v___x_4640_ = l_Lean_instantiateMVarsCore(v_mctx_4639_, v_e_4633_);
v_fst_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_fst_4641_);
v_snd_4642_ = lean_ctor_get(v___x_4640_, 1);
lean_inc(v_snd_4642_);
lean_dec_ref(v___x_4640_);
v___x_4643_ = lean_st_ref_take(v___y_4634_);
v_cache_4644_ = lean_ctor_get(v___x_4643_, 1);
v_zetaDeltaFVarIds_4645_ = lean_ctor_get(v___x_4643_, 2);
v_postponed_4646_ = lean_ctor_get(v___x_4643_, 3);
v_diag_4647_ = lean_ctor_get(v___x_4643_, 4);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4656_ == 0)
{
lean_object* v_unused_4657_; 
v_unused_4657_ = lean_ctor_get(v___x_4643_, 0);
lean_dec(v_unused_4657_);
v___x_4649_ = v___x_4643_;
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_diag_4647_);
lean_inc(v_postponed_4646_);
lean_inc(v_zetaDeltaFVarIds_4645_);
lean_inc(v_cache_4644_);
lean_dec(v___x_4643_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 0, v_snd_4642_);
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_snd_4642_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_cache_4644_);
lean_ctor_set(v_reuseFailAlloc_4655_, 2, v_zetaDeltaFVarIds_4645_);
lean_ctor_set(v_reuseFailAlloc_4655_, 3, v_postponed_4646_);
lean_ctor_set(v_reuseFailAlloc_4655_, 4, v_diag_4647_);
v___x_4652_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = lean_st_ref_put(v___y_4634_, v___x_4652_);
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v_fst_4641_);
return v___x_4654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg___boxed(lean_object* v_e_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4658_, v___y_4659_);
lean_dec(v___y_4659_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_e_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4662_, v___y_4664_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_e_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(v_e_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_opts_4676_, lean_object* v_opt_4677_){
_start:
{
lean_object* v_name_4678_; lean_object* v_map_4679_; lean_object* v___x_4680_; 
v_name_4678_ = lean_ctor_get(v_opt_4677_, 0);
v_map_4679_ = lean_ctor_get(v_opts_4676_, 0);
v___x_4680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4679_, v_name_4678_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v___x_4681_; 
v___x_4681_ = lean_box(0);
return v___x_4681_;
}
else
{
lean_object* v_val_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4692_; 
v_val_4682_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4684_ = v___x_4680_;
v_isShared_4685_ = v_isSharedCheck_4692_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_val_4682_);
lean_dec(v___x_4680_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4692_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
if (lean_obj_tag(v_val_4682_) == 1)
{
uint8_t v_v_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v_v_4686_ = lean_ctor_get_uint8(v_val_4682_, 0);
lean_dec_ref_known(v_val_4682_, 0);
v___x_4687_ = lean_box(v_v_4686_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4687_);
v___x_4689_ = v___x_4684_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
else
{
lean_object* v___x_4691_; 
lean_del_object(v___x_4684_);
lean_dec(v_val_4682_);
v___x_4691_ = lean_box(0);
return v___x_4691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_opts_4693_, lean_object* v_opt_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(v_opts_4693_, v_opt_4694_);
lean_dec_ref(v_opt_4694_);
lean_dec_ref(v_opts_4693_);
return v_res_4695_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_x_4696_, lean_object* v_x_4697_){
_start:
{
if (lean_obj_tag(v_x_4696_) == 0)
{
if (lean_obj_tag(v_x_4697_) == 0)
{
uint8_t v___x_4698_; 
v___x_4698_ = 1;
return v___x_4698_;
}
else
{
uint8_t v___x_4699_; 
v___x_4699_ = 0;
return v___x_4699_;
}
}
else
{
if (lean_obj_tag(v_x_4697_) == 0)
{
uint8_t v___x_4700_; 
v___x_4700_ = 0;
return v___x_4700_;
}
else
{
lean_object* v_val_4701_; uint8_t v___x_4702_; 
v_val_4701_ = lean_ctor_get(v_x_4697_, 0);
v___x_4702_ = lean_unbox(v_val_4701_);
if (v___x_4702_ == 0)
{
lean_object* v_val_4703_; uint8_t v___x_4704_; 
v_val_4703_ = lean_ctor_get(v_x_4696_, 0);
v___x_4704_ = lean_unbox(v_val_4703_);
if (v___x_4704_ == 0)
{
uint8_t v___x_4705_; 
v___x_4705_ = 1;
return v___x_4705_;
}
else
{
uint8_t v___x_4706_; 
v___x_4706_ = lean_unbox(v_val_4701_);
return v___x_4706_;
}
}
else
{
lean_object* v_val_4707_; uint8_t v___x_4708_; 
v_val_4707_ = lean_ctor_get(v_x_4696_, 0);
v___x_4708_ = lean_unbox(v_val_4707_);
return v___x_4708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_x_4709_, lean_object* v_x_4710_){
_start:
{
uint8_t v_res_4711_; lean_object* v_r_4712_; 
v_res_4711_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(v_x_4709_, v_x_4710_);
lean_dec(v_x_4710_);
lean_dec(v_x_4709_);
v_r_4712_ = lean_box(v_res_4711_);
return v_r_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_cls_4713_, lean_object* v_msg_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_ref_4720_; lean_object* v___x_4721_; lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4767_; 
v_ref_4720_ = lean_ctor_get(v___y_4717_, 2);
v___x_4721_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4767_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4767_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v_traceState_4727_; lean_object* v_env_4728_; lean_object* v_nextMacroScope_4729_; lean_object* v_ngen_4730_; lean_object* v_auxDeclNGen_4731_; lean_object* v_cache_4732_; lean_object* v_recordedDeps_4733_; lean_object* v_messages_4734_; lean_object* v_infoState_4735_; lean_object* v_snapshotTasks_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4766_; 
v___x_4726_ = lean_st_ref_take(v___y_4718_);
v_traceState_4727_ = lean_ctor_get(v___x_4726_, 4);
v_env_4728_ = lean_ctor_get(v___x_4726_, 0);
v_nextMacroScope_4729_ = lean_ctor_get(v___x_4726_, 1);
v_ngen_4730_ = lean_ctor_get(v___x_4726_, 2);
v_auxDeclNGen_4731_ = lean_ctor_get(v___x_4726_, 3);
v_cache_4732_ = lean_ctor_get(v___x_4726_, 5);
v_recordedDeps_4733_ = lean_ctor_get(v___x_4726_, 6);
v_messages_4734_ = lean_ctor_get(v___x_4726_, 7);
v_infoState_4735_ = lean_ctor_get(v___x_4726_, 8);
v_snapshotTasks_4736_ = lean_ctor_get(v___x_4726_, 9);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4738_ = v___x_4726_;
v_isShared_4739_ = v_isSharedCheck_4766_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_snapshotTasks_4736_);
lean_inc(v_infoState_4735_);
lean_inc(v_messages_4734_);
lean_inc(v_recordedDeps_4733_);
lean_inc(v_cache_4732_);
lean_inc(v_traceState_4727_);
lean_inc(v_auxDeclNGen_4731_);
lean_inc(v_ngen_4730_);
lean_inc(v_nextMacroScope_4729_);
lean_inc(v_env_4728_);
lean_dec(v___x_4726_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4766_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
uint64_t v_tid_4740_; lean_object* v_traces_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4765_; 
v_tid_4740_ = lean_ctor_get_uint64(v_traceState_4727_, sizeof(void*)*1);
v_traces_4741_ = lean_ctor_get(v_traceState_4727_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v_traceState_4727_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4743_ = v_traceState_4727_;
v_isShared_4744_ = v_isSharedCheck_4765_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_traces_4741_);
lean_dec(v_traceState_4727_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4765_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; double v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4745_ = lean_box(0);
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_4748_ = 0;
v___x_4749_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4750_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4750_, 0, v_cls_4713_);
lean_ctor_set(v___x_4750_, 1, v___x_4746_);
lean_ctor_set(v___x_4750_, 2, v___x_4749_);
lean_ctor_set_float(v___x_4750_, sizeof(void*)*3, v___x_4747_);
lean_ctor_set_float(v___x_4750_, sizeof(void*)*3 + 8, v___x_4747_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*3 + 16, v___x_4748_);
v___x_4751_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_4752_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v_a_4722_);
lean_ctor_set(v___x_4752_, 2, v___x_4751_);
lean_inc(v_ref_4720_);
v___x_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4753_, 0, v_ref_4720_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = l_Lean_PersistentArray_push___redArg(v_traces_4741_, v___x_4753_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4754_);
v___x_4756_ = v___x_4743_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4754_);
lean_ctor_set_uint64(v_reuseFailAlloc_4764_, sizeof(void*)*1, v_tid_4740_);
v___x_4756_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4758_; 
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 4, v___x_4756_);
v___x_4758_ = v___x_4738_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_env_4728_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_nextMacroScope_4729_);
lean_ctor_set(v_reuseFailAlloc_4763_, 2, v_ngen_4730_);
lean_ctor_set(v_reuseFailAlloc_4763_, 3, v_auxDeclNGen_4731_);
lean_ctor_set(v_reuseFailAlloc_4763_, 4, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4763_, 5, v_cache_4732_);
lean_ctor_set(v_reuseFailAlloc_4763_, 6, v_recordedDeps_4733_);
lean_ctor_set(v_reuseFailAlloc_4763_, 7, v_messages_4734_);
lean_ctor_set(v_reuseFailAlloc_4763_, 8, v_infoState_4735_);
lean_ctor_set(v_reuseFailAlloc_4763_, 9, v_snapshotTasks_4736_);
v___x_4758_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = lean_st_ref_put(v___y_4718_, v___x_4758_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v___x_4745_);
v___x_4761_ = v___x_4724_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4745_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_cls_4768_, lean_object* v_msg_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v_cls_4768_, v_msg_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(lean_object* v_o_4776_, lean_object* v_k_4777_, uint8_t v_v_4778_){
_start:
{
lean_object* v_map_4779_; uint8_t v_hasTrace_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4794_; 
v_map_4779_ = lean_ctor_get(v_o_4776_, 0);
v_hasTrace_4780_ = lean_ctor_get_uint8(v_o_4776_, sizeof(void*)*1);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_o_4776_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4782_ = v_o_4776_;
v_isShared_4783_ = v_isSharedCheck_4794_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_map_4779_);
lean_dec(v_o_4776_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4794_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4784_, 0, v_v_4778_);
lean_inc(v_k_4777_);
v___x_4785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4777_, v___x_4784_, v_map_4779_);
if (v_hasTrace_4780_ == 0)
{
lean_object* v___x_4786_; uint8_t v___x_4787_; lean_object* v___x_4789_; 
v___x_4786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4787_ = l_Lean_Name_isPrefixOf(v___x_4786_, v_k_4777_);
lean_dec(v_k_4777_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4785_);
v___x_4789_ = v___x_4782_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4785_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_ctor_set_uint8(v___x_4789_, sizeof(void*)*1, v___x_4787_);
return v___x_4789_;
}
}
else
{
lean_object* v___x_4792_; 
lean_dec(v_k_4777_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4785_);
v___x_4792_ = v___x_4782_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4793_, sizeof(void*)*1, v_hasTrace_4780_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5___boxed(lean_object* v_o_4795_, lean_object* v_k_4796_, lean_object* v_v_4797_){
_start:
{
uint8_t v_v_boxed_4798_; lean_object* v_res_4799_; 
v_v_boxed_4798_ = lean_unbox(v_v_4797_);
v_res_4799_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(v_o_4795_, v_k_4796_, v_v_boxed_4798_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4800_, lean_object* v_opt_4801_, uint8_t v_val_4802_){
_start:
{
lean_object* v_name_4803_; lean_object* v___x_4804_; 
v_name_4803_ = lean_ctor_get(v_opt_4801_, 0);
lean_inc(v_name_4803_);
lean_dec_ref(v_opt_4801_);
v___x_4804_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(v_opts_4800_, v_name_4803_, v_val_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4805_, lean_object* v_opt_4806_, lean_object* v_val_4807_){
_start:
{
uint8_t v_val_boxed_4808_; lean_object* v_res_4809_; 
v_val_boxed_4808_ = lean_unbox(v_val_4807_);
v_res_4809_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4805_, v_opt_4806_, v_val_boxed_4808_);
return v_res_4809_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__0(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4810_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4811_ = lean_unsigned_to_nat(2u);
v___x_4812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
lean_ctor_set(v___x_4812_, 1, v___x_4810_);
return v___x_4812_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4813_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__0, &l_Lean_PrettyPrinter_delabCore___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__0);
v___x_4814_ = lean_box(1);
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
lean_ctor_set(v___x_4816_, 1, v___x_4814_);
lean_ctor_set(v___x_4816_, 2, v___x_4813_);
return v___x_4816_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4820_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__4));
v___x_4821_ = lean_unsigned_to_nat(18u);
v___x_4822_ = lean_unsigned_to_nat(536u);
v___x_4823_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__3));
v___x_4824_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4825_ = l_mkPanicMessageWithDecl(v___x_4824_, v___x_4823_, v___x_4822_, v___x_4821_, v___x_4820_);
return v___x_4825_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4831_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4832_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4833_ = l_Lean_Name_append(v___x_4832_, v___x_4831_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4834_, lean_object* v_optionsPerPos_4835_, lean_object* v_delab_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_fst_4843_; lean_object* v_snd_4844_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v_optionsPerPos_4851_; lean_object* v___y_4852_; lean_object* v___y_4853_; lean_object* v___y_4854_; lean_object* v___y_4855_; lean_object* v___y_4912_; lean_object* v_e_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4931_; lean_object* v_e_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___x_4948_; 
v___x_4948_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4834_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4949_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4954_; uint8_t v___y_4955_; uint16_t v___y_4956_; lean_object* v___y_4957_; lean_object* v___y_4958_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; uint8_t v___y_4985_; lean_object* v___y_4986_; uint8_t v___y_4987_; uint16_t v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; uint8_t v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v_opts_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v_toCold_5068_; lean_object* v_options_5069_; uint8_t v_hasTrace_5070_; 
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___x_4948_, 1);
v_toCold_5068_ = lean_ctor_get(v_a_4839_, 0);
v_options_5069_ = lean_ctor_get(v_toCold_5068_, 2);
v_hasTrace_5070_ = lean_ctor_get_uint8(v_options_5069_, sizeof(void*)*1);
if (v_hasTrace_5070_ == 0)
{
v___y_5041_ = v_a_4837_;
v___y_5042_ = v_a_4838_;
v___y_5043_ = v_a_4839_;
v___y_5044_ = v_a_4840_;
goto v___jp_5040_;
}
else
{
lean_object* v_inheritedTraceOptions_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; 
v_inheritedTraceOptions_5071_ = lean_ctor_get(v_toCold_5068_, 11);
v___x_5072_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5073_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5071_, v_options_5069_, v___x_5073_);
if (v___x_5074_ == 0)
{
v___y_5041_ = v_a_4837_;
v___y_5042_ = v_a_4838_;
v___y_5043_ = v_a_4839_;
v___y_5044_ = v_a_4840_;
goto v___jp_5040_;
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5075_ = lean_expr_dbg_to_string(v_a_4949_);
v___x_5076_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
v___x_5077_ = l_Lean_MessageData_ofFormat(v___x_5076_);
v___x_5078_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5072_, v___x_5077_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_dec_ref_known(v___x_5078_, 1);
v___y_5041_ = v_a_4837_;
v___y_5042_ = v_a_4838_;
v___y_5043_ = v_a_4839_;
v___y_5044_ = v_a_4840_;
goto v___jp_5040_;
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v_a_4949_);
lean_dec_ref(v_delab_4836_);
lean_dec(v_optionsPerPos_4835_);
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5078_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5078_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
v___jp_4950_:
{
lean_object* v_toCold_4959_; lean_object* v_currRecDepth_4960_; lean_object* v_ref_4961_; uint8_t v_suppressElabErrors_4962_; uint8_t v_isRecordingDeps_4963_; lean_object* v_fileName_4964_; lean_object* v_fileMap_4965_; lean_object* v_currNamespace_4966_; lean_object* v_openDecls_4967_; lean_object* v_initHeartbeats_4968_; lean_object* v_maxHeartbeats_4969_; lean_object* v_quotContext_4970_; lean_object* v_currMacroScope_4971_; lean_object* v_cancelTk_x3f_4972_; lean_object* v_inheritedTraceOptions_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v_toCold_4959_ = lean_ctor_get(v___y_4957_, 0);
v_currRecDepth_4960_ = lean_ctor_get(v___y_4957_, 1);
v_ref_4961_ = lean_ctor_get(v___y_4957_, 2);
v_suppressElabErrors_4962_ = lean_ctor_get_uint8(v___y_4957_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4963_ = lean_ctor_get_uint8(v___y_4957_, sizeof(void*)*3 + 3);
v_fileName_4964_ = lean_ctor_get(v_toCold_4959_, 0);
v_fileMap_4965_ = lean_ctor_get(v_toCold_4959_, 1);
v_currNamespace_4966_ = lean_ctor_get(v_toCold_4959_, 4);
v_openDecls_4967_ = lean_ctor_get(v_toCold_4959_, 5);
v_initHeartbeats_4968_ = lean_ctor_get(v_toCold_4959_, 6);
v_maxHeartbeats_4969_ = lean_ctor_get(v_toCold_4959_, 7);
v_quotContext_4970_ = lean_ctor_get(v_toCold_4959_, 8);
v_currMacroScope_4971_ = lean_ctor_get(v_toCold_4959_, 9);
v_cancelTk_x3f_4972_ = lean_ctor_get(v_toCold_4959_, 10);
v_inheritedTraceOptions_4973_ = lean_ctor_get(v_toCold_4959_, 11);
v___x_4974_ = l_Lean_maxRecDepth;
v___x_4975_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v___y_4954_, v___x_4974_);
lean_inc_ref(v_inheritedTraceOptions_4973_);
lean_inc(v_cancelTk_x3f_4972_);
lean_inc(v_currMacroScope_4971_);
lean_inc(v_quotContext_4970_);
lean_inc(v_maxHeartbeats_4969_);
lean_inc(v_initHeartbeats_4968_);
lean_inc(v_openDecls_4967_);
lean_inc(v_currNamespace_4966_);
lean_inc_ref(v_fileMap_4965_);
lean_inc_ref(v_fileName_4964_);
v___x_4976_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4976_, 0, v_fileName_4964_);
lean_ctor_set(v___x_4976_, 1, v_fileMap_4965_);
lean_ctor_set(v___x_4976_, 2, v___y_4954_);
lean_ctor_set(v___x_4976_, 3, v___x_4975_);
lean_ctor_set(v___x_4976_, 4, v_currNamespace_4966_);
lean_ctor_set(v___x_4976_, 5, v_openDecls_4967_);
lean_ctor_set(v___x_4976_, 6, v_initHeartbeats_4968_);
lean_ctor_set(v___x_4976_, 7, v_maxHeartbeats_4969_);
lean_ctor_set(v___x_4976_, 8, v_quotContext_4970_);
lean_ctor_set(v___x_4976_, 9, v_currMacroScope_4971_);
lean_ctor_set(v___x_4976_, 10, v_cancelTk_x3f_4972_);
lean_ctor_set(v___x_4976_, 11, v_inheritedTraceOptions_4973_);
lean_inc(v_ref_4961_);
lean_inc(v_currRecDepth_4960_);
v___x_4977_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
lean_ctor_set(v___x_4977_, 1, v_currRecDepth_4960_);
lean_ctor_set(v___x_4977_, 2, v_ref_4961_);
lean_ctor_set_uint16(v___x_4977_, sizeof(void*)*3, v___y_4956_);
lean_ctor_set_uint8(v___x_4977_, sizeof(void*)*3 + 2, v_suppressElabErrors_4962_);
lean_ctor_set_uint8(v___x_4977_, sizeof(void*)*3 + 3, v_isRecordingDeps_4963_);
if (v___y_4955_ == 0)
{
v___y_4931_ = v___y_4953_;
v_e_4932_ = v_a_4949_;
v___y_4933_ = v___y_4952_;
v___y_4934_ = v___y_4951_;
v___y_4935_ = v___x_4977_;
v___y_4936_ = v___y_4958_;
goto v___jp_4930_;
}
else
{
lean_object* v___x_4978_; lean_object* v_a_4979_; 
v___x_4978_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_a_4949_, v___y_4951_);
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref(v___x_4978_);
v___y_4931_ = v___y_4953_;
v_e_4932_ = v_a_4979_;
v___y_4933_ = v___y_4952_;
v___y_4934_ = v___y_4951_;
v___y_4935_ = v___x_4977_;
v___y_4936_ = v___y_4958_;
goto v___jp_4930_;
}
}
v___jp_4980_:
{
lean_object* v___x_4990_; lean_object* v_env_4991_; lean_object* v_nextMacroScope_4992_; lean_object* v_ngen_4993_; lean_object* v_auxDeclNGen_4994_; lean_object* v_traceState_4995_; lean_object* v_recordedDeps_4996_; lean_object* v_messages_4997_; lean_object* v_infoState_4998_; lean_object* v_snapshotTasks_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5009_; 
v___x_4990_ = lean_st_ref_take(v___y_4986_);
v_env_4991_ = lean_ctor_get(v___x_4990_, 0);
v_nextMacroScope_4992_ = lean_ctor_get(v___x_4990_, 1);
v_ngen_4993_ = lean_ctor_get(v___x_4990_, 2);
v_auxDeclNGen_4994_ = lean_ctor_get(v___x_4990_, 3);
v_traceState_4995_ = lean_ctor_get(v___x_4990_, 4);
v_recordedDeps_4996_ = lean_ctor_get(v___x_4990_, 6);
v_messages_4997_ = lean_ctor_get(v___x_4990_, 7);
v_infoState_4998_ = lean_ctor_get(v___x_4990_, 8);
v_snapshotTasks_4999_ = lean_ctor_get(v___x_4990_, 9);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5009_ == 0)
{
lean_object* v_unused_5010_; 
v_unused_5010_ = lean_ctor_get(v___x_4990_, 5);
lean_dec(v_unused_5010_);
v___x_5001_ = v___x_4990_;
v_isShared_5002_ = v_isSharedCheck_5009_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_snapshotTasks_4999_);
lean_inc(v_infoState_4998_);
lean_inc(v_messages_4997_);
lean_inc(v_recordedDeps_4996_);
lean_inc(v_traceState_4995_);
lean_inc(v_auxDeclNGen_4994_);
lean_inc(v_ngen_4993_);
lean_inc(v_nextMacroScope_4992_);
lean_inc(v_env_4991_);
lean_dec(v___x_4990_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5009_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_5003_ = l_Lean_Kernel_enableDiag(v_env_4991_, v___y_4987_);
v___x_5004_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1);
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 5, v___x_5004_);
lean_ctor_set(v___x_5001_, 0, v___x_5003_);
v___x_5006_ = v___x_5001_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5008_, 1, v_nextMacroScope_4992_);
lean_ctor_set(v_reuseFailAlloc_5008_, 2, v_ngen_4993_);
lean_ctor_set(v_reuseFailAlloc_5008_, 3, v_auxDeclNGen_4994_);
lean_ctor_set(v_reuseFailAlloc_5008_, 4, v_traceState_4995_);
lean_ctor_set(v_reuseFailAlloc_5008_, 5, v___x_5004_);
lean_ctor_set(v_reuseFailAlloc_5008_, 6, v_recordedDeps_4996_);
lean_ctor_set(v_reuseFailAlloc_5008_, 7, v_messages_4997_);
lean_ctor_set(v_reuseFailAlloc_5008_, 8, v_infoState_4998_);
lean_ctor_set(v_reuseFailAlloc_5008_, 9, v_snapshotTasks_4999_);
v___x_5006_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_st_ref_put(v___y_4986_, v___x_5006_);
v___y_4951_ = v___y_4981_;
v___y_4952_ = v___y_4982_;
v___y_4953_ = v___y_4984_;
v___y_4954_ = v___y_4983_;
v___y_4955_ = v___y_4985_;
v___y_4956_ = v___y_4988_;
v___y_4957_ = v___y_4989_;
v___y_4958_ = v___y_4986_;
goto v___jp_4950_;
}
}
}
v___jp_5011_:
{
uint16_t v___x_5019_; lean_object* v___x_5020_; lean_object* v_env_5021_; uint8_t v___x_5022_; uint16_t v___x_5023_; uint16_t v___x_5024_; uint16_t v___x_5025_; uint8_t v___x_5026_; 
v___x_5019_ = l_Lean_OptionFlags_ofOptions(v___y_5018_);
v___x_5020_ = lean_st_ref_get(v___y_5015_);
v_env_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc_ref(v_env_5021_);
lean_dec(v___x_5020_);
v___x_5022_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5021_);
lean_dec_ref(v_env_5021_);
v___x_5023_ = 512;
v___x_5024_ = lean_uint16_land(v___x_5019_, v___x_5023_);
v___x_5025_ = 0;
v___x_5026_ = lean_uint16_dec_eq(v___x_5024_, v___x_5025_);
if (v___x_5026_ == 0)
{
if (v___x_5022_ == 0)
{
uint8_t v___x_5027_; 
v___x_5027_ = 1;
v___y_4981_ = v___y_5012_;
v___y_4982_ = v___y_5013_;
v___y_4983_ = v___y_5018_;
v___y_4984_ = v___y_5014_;
v___y_4985_ = v___y_5016_;
v___y_4986_ = v___y_5015_;
v___y_4987_ = v___x_5027_;
v___y_4988_ = v___x_5019_;
v___y_4989_ = v___y_5017_;
goto v___jp_4980_;
}
else
{
v___y_4951_ = v___y_5012_;
v___y_4952_ = v___y_5013_;
v___y_4953_ = v___y_5014_;
v___y_4954_ = v___y_5018_;
v___y_4955_ = v___y_5016_;
v___y_4956_ = v___x_5019_;
v___y_4957_ = v___y_5017_;
v___y_4958_ = v___y_5015_;
goto v___jp_4950_;
}
}
else
{
if (v___x_5022_ == 0)
{
v___y_4951_ = v___y_5012_;
v___y_4952_ = v___y_5013_;
v___y_4953_ = v___y_5014_;
v___y_4954_ = v___y_5018_;
v___y_4955_ = v___y_5016_;
v___y_4956_ = v___x_5019_;
v___y_4957_ = v___y_5017_;
v___y_4958_ = v___y_5015_;
goto v___jp_4950_;
}
else
{
uint8_t v___x_5028_; 
v___x_5028_ = 0;
v___y_4981_ = v___y_5012_;
v___y_4982_ = v___y_5013_;
v___y_4983_ = v___y_5018_;
v___y_4984_ = v___y_5014_;
v___y_4985_ = v___y_5016_;
v___y_4986_ = v___y_5015_;
v___y_4987_ = v___x_5028_;
v___y_4988_ = v___x_5019_;
v___y_4989_ = v___y_5017_;
goto v___jp_4980_;
}
}
}
v___jp_5029_:
{
lean_object* v_toCold_5035_; uint8_t v_isRecordingDeps_5036_; uint8_t v___x_5037_; 
v_toCold_5035_ = lean_ctor_get(v___y_5033_, 0);
v_isRecordingDeps_5036_ = lean_ctor_get_uint8(v___y_5033_, sizeof(void*)*3 + 3);
v___x_5037_ = l_Lean_getPPInstantiateMVars(v_opts_5030_);
if (v_isRecordingDeps_5036_ == 0)
{
lean_inc_ref(v_opts_5030_);
v___y_5012_ = v___y_5032_;
v___y_5013_ = v___y_5031_;
v___y_5014_ = v_opts_5030_;
v___y_5015_ = v___y_5034_;
v___y_5016_ = v___x_5037_;
v___y_5017_ = v___y_5033_;
v___y_5018_ = v_opts_5030_;
goto v___jp_5011_;
}
else
{
lean_object* v_options_5038_; lean_object* v___x_5039_; 
v_options_5038_ = lean_ctor_get(v_toCold_5035_, 2);
lean_inc_ref(v_options_5038_);
v___x_5039_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5038_);
v___y_5012_ = v___y_5032_;
v___y_5013_ = v___y_5031_;
v___y_5014_ = v_opts_5030_;
v___y_5015_ = v___y_5034_;
v___y_5016_ = v___x_5037_;
v___y_5017_ = v___y_5033_;
v___y_5018_ = v___x_5039_;
goto v___jp_5011_;
}
}
v___jp_5040_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5045_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5043_);
v___x_5046_ = l_Lean_pp_proofs;
v___x_5047_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(v___x_5045_, v___x_5046_);
v___x_5048_ = lean_box(0);
v___x_5049_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(v___x_5047_, v___x_5048_);
lean_dec(v___x_5047_);
if (v___x_5049_ == 0)
{
v_opts_5030_ = v___x_5045_;
v___y_5031_ = v___y_5041_;
v___y_5032_ = v___y_5042_;
v___y_5033_ = v___y_5043_;
v___y_5034_ = v___y_5044_;
goto v___jp_5029_;
}
else
{
uint8_t v___x_5050_; 
v___x_5050_ = l_Lean_Expr_isConst(v_a_4949_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; 
lean_inc(v_a_4949_);
v___x_5051_ = l_Lean_Meta_isProof(v_a_4949_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; uint8_t v___x_5053_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v___x_5053_ = lean_unbox(v_a_5052_);
lean_dec(v_a_5052_);
if (v___x_5053_ == 0)
{
v_opts_5030_ = v___x_5045_;
v___y_5031_ = v___y_5041_;
v___y_5032_ = v___y_5042_;
v___y_5033_ = v___y_5043_;
v___y_5034_ = v___y_5044_;
goto v___jp_5029_;
}
else
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(v___x_5045_, v___x_5046_, v___x_5049_);
v_opts_5030_ = v___x_5054_;
v___y_5031_ = v___y_5041_;
v___y_5032_ = v___y_5042_;
v___y_5033_ = v___y_5043_;
v___y_5034_ = v___y_5044_;
goto v___jp_5029_;
}
}
else
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5067_; 
v_a_5055_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5057_ = v___x_5051_;
v_isShared_5058_ = v_isSharedCheck_5067_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v___x_5051_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5067_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
uint8_t v___x_5059_; 
v___x_5059_ = l_Lean_Exception_isInterrupt(v_a_5055_);
if (v___x_5059_ == 0)
{
uint8_t v___x_5060_; 
lean_inc(v_a_5055_);
v___x_5060_ = l_Lean_Exception_isRuntime(v_a_5055_);
if (v___x_5060_ == 0)
{
lean_del_object(v___x_5057_);
lean_dec(v_a_5055_);
v_opts_5030_ = v___x_5045_;
v___y_5031_ = v___y_5041_;
v___y_5032_ = v___y_5042_;
v___y_5033_ = v___y_5043_;
v___y_5034_ = v___y_5044_;
goto v___jp_5029_;
}
else
{
lean_object* v___x_5062_; 
lean_dec_ref(v___x_5045_);
lean_dec(v_a_4949_);
lean_dec_ref(v_delab_4836_);
lean_dec(v_optionsPerPos_4835_);
if (v_isShared_5058_ == 0)
{
v___x_5062_ = v___x_5057_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5055_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
else
{
lean_object* v___x_5065_; 
lean_dec_ref(v___x_5045_);
lean_dec(v_a_4949_);
lean_dec_ref(v_delab_4836_);
lean_dec(v_optionsPerPos_4835_);
if (v_isShared_5058_ == 0)
{
v___x_5065_ = v___x_5057_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5055_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
}
else
{
v_opts_5030_ = v___x_5045_;
v___y_5031_ = v___y_5041_;
v___y_5032_ = v___y_5042_;
v___y_5033_ = v___y_5043_;
v___y_5034_ = v___y_5044_;
goto v___jp_5029_;
}
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec_ref(v_delab_4836_);
lean_dec(v_optionsPerPos_4835_);
v_a_5087_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_4948_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_4948_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
v___jp_4842_:
{
lean_object* v_infos_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v_infos_4845_ = lean_ctor_get(v_snd_4844_, 1);
lean_inc(v_infos_4845_);
lean_dec_ref(v_snd_4844_);
v___x_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4846_, 0, v_fst_4843_);
lean_ctor_set(v___x_4846_, 1, v_infos_4845_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
return v___x_4847_;
}
v___jp_4848_:
{
lean_object* v_toCold_4856_; lean_object* v_currRecDepth_4857_; uint16_t v_optionFlags_4858_; uint8_t v_suppressElabErrors_4859_; uint8_t v_isRecordingDeps_4860_; lean_object* v_currNamespace_4861_; lean_object* v_openDecls_4862_; lean_object* v_lctx_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_toCold_4856_ = lean_ctor_get(v___y_4854_, 0);
v_currRecDepth_4857_ = lean_ctor_get(v___y_4854_, 1);
v_optionFlags_4858_ = lean_ctor_get_uint16(v___y_4854_, sizeof(void*)*3);
v_suppressElabErrors_4859_ = lean_ctor_get_uint8(v___y_4854_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4860_ = lean_ctor_get_uint8(v___y_4854_, sizeof(void*)*3 + 3);
v_currNamespace_4861_ = lean_ctor_get(v_toCold_4856_, 4);
v_openDecls_4862_ = lean_ctor_get(v_toCold_4856_, 5);
v_lctx_4863_ = lean_ctor_get(v___y_4852_, 2);
v___x_4864_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4865_ = lean_box(0);
v___x_4866_ = l_Lean_Options_getInPattern(v___y_4850_);
lean_dec_ref(v___y_4850_);
v___x_4867_ = l_Lean_SubExpr_mkRoot(v___y_4849_);
v___x_4868_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4863_);
v___x_4869_ = lean_local_ctx_num_indices(v_lctx_4863_);
lean_inc(v_openDecls_4862_);
lean_inc(v_currNamespace_4861_);
v___x_4870_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4870_, 0, v_optionsPerPos_4851_);
lean_ctor_set(v___x_4870_, 1, v_currNamespace_4861_);
lean_ctor_set(v___x_4870_, 2, v_openDecls_4862_);
lean_ctor_set(v___x_4870_, 3, v___x_4867_);
lean_ctor_set(v___x_4870_, 4, v___x_4868_);
lean_ctor_set(v___x_4870_, 5, v___x_4869_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*6, v___x_4866_);
v___x_4871_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__1, &l_Lean_PrettyPrinter_delabCore___redArg___closed__1_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__1);
v___x_4872_ = lean_st_mk_ref(v___x_4871_);
lean_inc(v_currRecDepth_4857_);
lean_inc_ref(v_toCold_4856_);
v___x_4873_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4873_, 0, v_toCold_4856_);
lean_ctor_set(v___x_4873_, 1, v_currRecDepth_4857_);
lean_ctor_set(v___x_4873_, 2, v___x_4865_);
lean_ctor_set_uint16(v___x_4873_, sizeof(void*)*3, v_optionFlags_4858_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*3 + 2, v_suppressElabErrors_4859_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*3 + 3, v_isRecordingDeps_4860_);
lean_inc(v___y_4855_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
lean_inc(v___x_4872_);
v___x_4874_ = lean_apply_7(v_delab_4836_, v___x_4870_, v___x_4872_, v___y_4852_, v___y_4853_, v___x_4873_, v___y_4855_, lean_box(0));
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
lean_dec_ref(v___y_4854_);
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v___x_4876_ = lean_st_ref_get(v___x_4872_);
lean_dec(v___x_4872_);
v_fst_4843_ = v_a_4875_;
v_snd_4844_ = v___x_4876_;
goto v___jp_4842_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v___x_4872_);
v_a_4877_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4879_ = v___x_4874_;
v_isShared_4880_ = v_isSharedCheck_4910_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4874_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4910_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
uint8_t v___x_4881_; 
v___x_4881_ = l_Lean_Exception_isInterrupt(v_a_4877_);
if (v___x_4881_ == 0)
{
uint8_t v___x_4882_; 
lean_inc(v_a_4877_);
v___x_4882_ = l_Lean_Exception_isRuntime(v_a_4877_);
if (v___x_4882_ == 0)
{
if (lean_obj_tag(v_a_4877_) == 0)
{
lean_object* v___x_4884_; 
lean_dec_ref(v___y_4854_);
if (v_isShared_4880_ == 0)
{
v___x_4884_ = v___x_4879_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4877_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
else
{
lean_object* v_id_4886_; uint8_t v___x_4887_; 
v_id_4886_ = lean_ctor_get(v_a_4877_, 0);
v___x_4887_ = l_Lean_instBEqInternalExceptionId_beq(v___x_4864_, v_id_4886_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4889_; 
lean_dec_ref(v___y_4854_);
if (v_isShared_4880_ == 0)
{
v___x_4889_ = v___x_4879_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4877_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
else
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
lean_dec_ref_known(v_a_4877_, 2);
lean_del_object(v___x_4879_);
v___x_4891_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4892_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4891_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
lean_dec_ref(v___y_4854_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v_fst_4894_; lean_object* v_snd_4895_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v_fst_4894_ = lean_ctor_get(v_a_4893_, 0);
lean_inc(v_fst_4894_);
v_snd_4895_ = lean_ctor_get(v_a_4893_, 1);
lean_inc(v_snd_4895_);
lean_dec(v_a_4893_);
v_fst_4843_ = v_fst_4894_;
v_snd_4844_ = v_snd_4895_;
goto v___jp_4842_;
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4892_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4892_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
}
else
{
lean_object* v___x_4905_; 
lean_dec_ref(v___y_4854_);
if (v_isShared_4880_ == 0)
{
v___x_4905_ = v___x_4879_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4877_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
else
{
lean_object* v___x_4908_; 
lean_dec_ref(v___y_4854_);
if (v_isShared_4880_ == 0)
{
v___x_4908_ = v___x_4879_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4877_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
}
v___jp_4911_:
{
uint8_t v___x_4918_; 
v___x_4918_ = l_Lean_getPPAll(v___y_4912_);
if (v___x_4918_ == 0)
{
uint8_t v___x_4919_; 
v___x_4919_ = l_Lean_getPPAnalyze(v___y_4912_);
if (v___x_4919_ == 0)
{
v___y_4849_ = v_e_4913_;
v___y_4850_ = v___y_4912_;
v_optionsPerPos_4851_ = v_optionsPerPos_4835_;
v___y_4852_ = v___y_4914_;
v___y_4853_ = v___y_4915_;
v___y_4854_ = v___y_4916_;
v___y_4855_ = v___y_4917_;
goto v___jp_4848_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4835_) == 0)
{
v___y_4849_ = v_e_4913_;
v___y_4850_ = v___y_4912_;
v_optionsPerPos_4851_ = v_optionsPerPos_4835_;
v___y_4852_ = v___y_4914_;
v___y_4853_ = v___y_4915_;
v___y_4854_ = v___y_4916_;
v___y_4855_ = v___y_4917_;
goto v___jp_4848_;
}
else
{
lean_object* v___x_4920_; 
lean_inc_ref(v_e_4913_);
v___x_4920_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v___y_4849_ = v_e_4913_;
v___y_4850_ = v___y_4912_;
v_optionsPerPos_4851_ = v_a_4921_;
v___y_4852_ = v___y_4914_;
v___y_4853_ = v___y_4915_;
v___y_4854_ = v___y_4916_;
v___y_4855_ = v___y_4917_;
goto v___jp_4848_;
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec_ref(v___y_4916_);
lean_dec_ref(v_e_4913_);
lean_dec_ref(v___y_4912_);
lean_dec_ref(v_delab_4836_);
v_a_4922_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4920_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4920_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
}
else
{
v___y_4849_ = v_e_4913_;
v___y_4850_ = v___y_4912_;
v_optionsPerPos_4851_ = v_optionsPerPos_4835_;
v___y_4852_ = v___y_4914_;
v___y_4853_ = v___y_4915_;
v___y_4854_ = v___y_4916_;
v___y_4855_ = v___y_4917_;
goto v___jp_4848_;
}
}
v___jp_4930_:
{
uint8_t v___x_4937_; 
v___x_4937_ = l_Lean_getPPBeta(v___y_4931_);
if (v___x_4937_ == 0)
{
v___y_4912_ = v___y_4931_;
v_e_4913_ = v_e_4932_;
v___y_4914_ = v___y_4933_;
v___y_4915_ = v___y_4934_;
v___y_4916_ = v___y_4935_;
v___y_4917_ = v___y_4936_;
goto v___jp_4911_;
}
else
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Core_betaReduce(v_e_4932_, v___y_4935_, v___y_4936_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v___y_4912_ = v___y_4931_;
v_e_4913_ = v_a_4939_;
v___y_4914_ = v___y_4933_;
v___y_4915_ = v___y_4934_;
v___y_4916_ = v___y_4935_;
v___y_4917_ = v___y_4936_;
goto v___jp_4911_;
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec_ref(v___y_4935_);
lean_dec_ref(v___y_4931_);
lean_dec_ref(v_delab_4836_);
lean_dec(v_optionsPerPos_4835_);
v_a_4940_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4938_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4938_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5095_, lean_object* v_optionsPerPos_5096_, lean_object* v_delab_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5095_, v_optionsPerPos_5096_, v_delab_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5104_, lean_object* v_e_5105_, lean_object* v_optionsPerPos_5106_, lean_object* v_delab_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5105_, v_optionsPerPos_5106_, v_delab_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5114_, lean_object* v_e_5115_, lean_object* v_optionsPerPos_5116_, lean_object* v_delab_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5114_, v_e_5115_, v_optionsPerPos_5116_, v_delab_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5125_, lean_object* v_optionsPerPos_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5133_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5125_, v_optionsPerPos_5126_, v___x_5132_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5142_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5136_ = v___x_5133_;
v_isShared_5137_ = v_isSharedCheck_5142_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5133_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5142_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v_fst_5138_; lean_object* v___x_5140_; 
v_fst_5138_ = lean_ctor_get(v_a_5134_, 0);
lean_inc(v_fst_5138_);
lean_dec(v_a_5134_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 0, v_fst_5138_);
v___x_5140_ = v___x_5136_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_fst_5138_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
v_a_5143_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5133_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5133_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5151_, lean_object* v_optionsPerPos_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Lean_PrettyPrinter_delab(v_e_5151_, v_optionsPerPos_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5223_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5224_ = 0;
v___x_5225_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5226_ = l_Lean_registerTraceClass(v___x_5223_, v___x_5224_, v___x_5225_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_object* v___x_5227_; lean_object* v___x_5228_; 
lean_dec_ref_known(v___x_5226_, 1);
v___x_5227_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5228_ = l_Lean_registerTraceClass(v___x_5227_, v___x_5224_, v___x_5225_);
return v___x_5228_;
}
else
{
return v___x_5226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5230_;
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
