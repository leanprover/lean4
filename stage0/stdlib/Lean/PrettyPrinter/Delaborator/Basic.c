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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object*, lean_object*);
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
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_ctor_set(v___x_385_, 3, v___x_384_);
lean_ctor_set(v___x_385_, 4, v___x_383_);
lean_ctor_set(v___x_385_, 5, v___x_383_);
lean_ctor_set(v___x_385_, 6, v___x_383_);
lean_ctor_set(v___x_385_, 7, v___x_383_);
lean_ctor_set(v___x_385_, 8, v___x_383_);
lean_ctor_set(v___x_385_, 9, v___x_383_);
lean_ctor_set(v___x_385_, 10, v___x_383_);
lean_ctor_set(v___x_385_, 11, v___x_382_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(32u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((size_t)5ULL);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_unsigned_to_nat(32u);
v___x_392_ = lean_mk_empty_array_with_capacity(v___x_391_);
v___x_393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_394_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_390_);
lean_ctor_set(v___x_394_, 3, v___x_390_);
lean_ctor_set_usize(v___x_394_, 4, v___x_389_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(1);
v___x_396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_420_, lean_object* v_declHint_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_env_426_; uint8_t v___x_427_; 
v___x_424_ = lean_box(0);
v___x_425_ = lean_st_ref_get(v___y_422_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_Name_isAnonymous(v_declHint_421_);
if (v___x_427_ == 0)
{
uint8_t v_isExporting_428_; 
v_isExporting_428_ = lean_ctor_get_uint8(v_env_426_, sizeof(void*)*13);
if (v_isExporting_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec_ref(v_env_426_);
lean_dec(v_declHint_421_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_msg_420_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
lean_inc_ref(v_env_426_);
v___x_430_ = l_Lean_Environment_setExporting(v_env_426_, v___x_427_);
lean_inc(v_declHint_421_);
lean_inc_ref(v___x_430_);
v___x_431_ = l_Lean_Environment_contains(v___x_430_, v_declHint_421_, v_isExporting_428_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec_ref(v___x_430_);
lean_dec_ref(v_env_426_);
lean_dec(v_declHint_421_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_msg_420_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_c_438_; lean_object* v___x_439_; 
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_434_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_435_ = l_Lean_Options_empty;
v___x_436_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_436_, 0, v___x_430_);
lean_ctor_set(v___x_436_, 1, v___x_433_);
lean_ctor_set(v___x_436_, 2, v___x_434_);
lean_ctor_set(v___x_436_, 3, v___x_435_);
lean_inc(v_declHint_421_);
v___x_437_ = l_Lean_MessageData_ofConstName(v_declHint_421_, v___x_427_);
v_c_438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_438_, 0, v___x_436_);
lean_ctor_set(v_c_438_, 1, v___x_437_);
v___x_439_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_426_, v_declHint_421_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v_env_426_);
lean_dec(v_declHint_421_);
v___x_440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_c_438_);
v___x_442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_MessageData_note(v___x_443_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v_msg_420_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_481_; 
v_val_447_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_481_ == 0)
{
v___x_449_ = v___x_439_;
v_isShared_450_ = v_isSharedCheck_481_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v___x_439_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_481_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v_moduleNames_452_; lean_object* v_mod_453_; uint8_t v___x_454_; 
v___x_451_ = l_Lean_Environment_header(v_env_426_);
lean_dec_ref(v_env_426_);
v_moduleNames_452_ = lean_ctor_get(v___x_451_, 4);
lean_inc_ref(v_moduleNames_452_);
lean_dec_ref(v___x_451_);
v_mod_453_ = lean_array_get(v___x_424_, v_moduleNames_452_, v_val_447_);
lean_dec(v_val_447_);
lean_dec_ref(v_moduleNames_452_);
v___x_454_ = l_Lean_isPrivateName(v_declHint_421_);
lean_dec(v_declHint_421_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_c_438_);
v___x_457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_MessageData_ofName(v_mod_453_);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_MessageData_note(v___x_462_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v_msg_420_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
lean_ctor_set(v___x_449_, 0, v___x_464_);
v___x_466_ = v___x_449_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_c_438_);
v___x_470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Lean_MessageData_ofName(v_mod_453_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_MessageData_note(v___x_475_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v_msg_420_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
lean_ctor_set(v___x_449_, 0, v___x_477_);
v___x_479_ = v___x_449_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v_env_426_);
lean_dec(v_declHint_421_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_msg_420_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_483_, lean_object* v_declHint_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_483_, v_declHint_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object* v_msg_488_, lean_object* v_declHint_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
v___x_493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_488_, v_declHint_489_, v___y_491_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_503_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = l_Lean_unknownIdentifierMessageTag;
v___x_499_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_a_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_504_, lean_object* v_declHint_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_504_, v_declHint_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_toCold_515_; lean_object* v_env_516_; lean_object* v_options_517_; uint8_t v___x_518_; lean_object* v_env_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_514_ = lean_st_ref_get(v___y_512_);
v_toCold_515_ = lean_ctor_get(v___y_511_, 0);
v_env_516_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_514_);
v_options_517_ = lean_ctor_get(v_toCold_515_, 2);
v___x_518_ = 0;
v_env_519_ = l_Lean_Environment_setRecordingDeps(v_env_516_, v___x_518_);
v___x_520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_521_ = lean_unsigned_to_nat(32u);
v___x_522_ = lean_mk_empty_array_with_capacity(v___x_521_);
lean_dec_ref(v___x_522_);
v___x_523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_517_);
v___x_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_524_, 0, v_env_519_);
lean_ctor_set(v___x_524_, 1, v___x_520_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
lean_ctor_set(v___x_524_, 3, v_options_517_);
v___x_525_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_msgData_510_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msgData_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_ref_536_; lean_object* v___x_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_ref_536_ = lean_ctor_get(v___y_533_, 2);
v___x_537_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_532_, v___y_533_, v___y_534_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v_ref_536_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_ref_536_);
lean_ctor_set(v___x_542_, 1, v_a_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 1);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_toCold_557_; lean_object* v_currRecDepth_558_; lean_object* v_ref_559_; uint16_t v_optionFlags_560_; uint8_t v_suppressElabErrors_561_; uint8_t v_isRecordingDeps_562_; lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_toCold_557_ = lean_ctor_get(v___y_554_, 0);
v_currRecDepth_558_ = lean_ctor_get(v___y_554_, 1);
v_ref_559_ = lean_ctor_get(v___y_554_, 2);
v_optionFlags_560_ = lean_ctor_get_uint16(v___y_554_, sizeof(void*)*3);
v_suppressElabErrors_561_ = lean_ctor_get_uint8(v___y_554_, sizeof(void*)*3 + 2);
v_isRecordingDeps_562_ = lean_ctor_get_uint8(v___y_554_, sizeof(void*)*3 + 3);
v_ref_563_ = l_Lean_replaceRef(v_ref_552_, v_ref_559_);
lean_inc(v_currRecDepth_558_);
lean_inc_ref(v_toCold_557_);
v___x_564_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_564_, 0, v_toCold_557_);
lean_ctor_set(v___x_564_, 1, v_currRecDepth_558_);
lean_ctor_set(v___x_564_, 2, v_ref_563_);
lean_ctor_set_uint16(v___x_564_, sizeof(void*)*3, v_optionFlags_560_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3 + 2, v_suppressElabErrors_561_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*3 + 3, v_isRecordingDeps_562_);
v___x_565_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_553_, v___x_564_, v___y_555_);
lean_dec_ref_known(v___x_564_, 3);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_566_, v_msg_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v_ref_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_572_, lean_object* v_msg_573_, lean_object* v_declHint_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_580_; 
v___x_578_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_573_, v_declHint_574_, v___y_575_, v___y_576_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_572_, v_a_579_, v___y_575_, v___y_576_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_581_, lean_object* v_msg_582_, lean_object* v_declHint_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_581_, v_msg_582_, v_declHint_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v_ref_581_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object* v_ref_594_, lean_object* v_constName_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_599_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1);
v___x_600_ = 0;
lean_inc(v_constName_595_);
v___x_601_ = l_Lean_MessageData_ofConstName(v_constName_595_, v___x_600_);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_594_, v___x_604_, v_constName_595_, v___y_596_, v___y_597_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_ref_606_, lean_object* v_constName_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_606_, v_constName_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v_ref_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object* v_constName_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_ref_616_; lean_object* v___x_617_; 
v_ref_616_ = lean_ctor_get(v___y_613_, 2);
v___x_617_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_616_, v_constName_612_, v___y_613_, v___y_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_constName_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_constName_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_env_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_st_ref_get(v___y_625_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_627_);
v___x_629_ = 0;
lean_inc(v_constName_623_);
v___x_630_ = l_Lean_Environment_findConstVal_x3f(v_env_628_, v_constName_623_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_623_, v___y_624_, v___y_625_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_constName_623_);
v_val_632_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 0);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_val_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_constName_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
if (lean_obj_tag(v_a_645_) == 0)
{
lean_object* v___x_647_; 
v___x_647_ = l_List_reverse___redArg(v_a_646_);
return v___x_647_;
}
else
{
lean_object* v_head_648_; lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_head_648_ = lean_ctor_get(v_a_645_, 0);
v_tail_649_ = lean_ctor_get(v_a_645_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_651_ = v_a_645_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_inc(v_head_648_);
lean_dec(v_a_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = l_Lean_mkLevelParam(v_head_648_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v_a_646_);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_646_);
v___x_655_ = v_reuseFailAlloc_657_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v_a_645_ = v_tail_649_;
v_a_646_ = v___x_655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_constName_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
lean_inc(v_constName_659_);
v___x_663_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_675_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_675_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_levelParams_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v_levelParams_668_ = lean_ctor_get(v_a_664_, 1);
lean_inc(v_levelParams_668_);
lean_dec(v_a_664_);
v___x_669_ = lean_box(0);
v___x_670_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_levelParams_668_, v___x_669_);
v___x_671_ = l_Lean_mkConst(v_constName_659_, v___x_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_671_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_constName_659_);
v_a_676_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_663_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_663_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_constName_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_constName_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_t_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; lean_object* v_infoState_693_; uint8_t v_enabled_694_; 
v___x_692_ = lean_st_ref_get(v___y_690_);
v_infoState_693_ = lean_ctor_get(v___x_692_, 8);
lean_inc_ref(v_infoState_693_);
lean_dec(v___x_692_);
v_enabled_694_ = lean_ctor_get_uint8(v_infoState_693_, sizeof(void*)*3);
lean_dec_ref(v_infoState_693_);
if (v_enabled_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref(v_t_689_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v_infoState_698_; lean_object* v_env_699_; lean_object* v_nextMacroScope_700_; lean_object* v_ngen_701_; lean_object* v_auxDeclNGen_702_; lean_object* v_traceState_703_; lean_object* v_cache_704_; lean_object* v_recordedDeps_705_; lean_object* v_messages_706_; lean_object* v_snapshotTasks_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_729_; 
v___x_697_ = lean_st_ref_take(v___y_690_);
v_infoState_698_ = lean_ctor_get(v___x_697_, 8);
v_env_699_ = lean_ctor_get(v___x_697_, 0);
v_nextMacroScope_700_ = lean_ctor_get(v___x_697_, 1);
v_ngen_701_ = lean_ctor_get(v___x_697_, 2);
v_auxDeclNGen_702_ = lean_ctor_get(v___x_697_, 3);
v_traceState_703_ = lean_ctor_get(v___x_697_, 4);
v_cache_704_ = lean_ctor_get(v___x_697_, 5);
v_recordedDeps_705_ = lean_ctor_get(v___x_697_, 6);
v_messages_706_ = lean_ctor_get(v___x_697_, 7);
v_snapshotTasks_707_ = lean_ctor_get(v___x_697_, 9);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_729_ == 0)
{
v___x_709_ = v___x_697_;
v_isShared_710_ = v_isSharedCheck_729_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_snapshotTasks_707_);
lean_inc(v_infoState_698_);
lean_inc(v_messages_706_);
lean_inc(v_recordedDeps_705_);
lean_inc(v_cache_704_);
lean_inc(v_traceState_703_);
lean_inc(v_auxDeclNGen_702_);
lean_inc(v_ngen_701_);
lean_inc(v_nextMacroScope_700_);
lean_inc(v_env_699_);
lean_dec(v___x_697_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_729_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
uint8_t v_enabled_711_; lean_object* v_assignment_712_; lean_object* v_lazyAssignment_713_; lean_object* v_trees_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_728_; 
v_enabled_711_ = lean_ctor_get_uint8(v_infoState_698_, sizeof(void*)*3);
v_assignment_712_ = lean_ctor_get(v_infoState_698_, 0);
v_lazyAssignment_713_ = lean_ctor_get(v_infoState_698_, 1);
v_trees_714_ = lean_ctor_get(v_infoState_698_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_infoState_698_);
if (v_isSharedCheck_728_ == 0)
{
v___x_716_ = v_infoState_698_;
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_trees_714_);
lean_inc(v_lazyAssignment_713_);
lean_inc(v_assignment_712_);
lean_dec(v_infoState_698_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_PersistentArray_push___redArg(v_trees_714_, v_t_689_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_assignment_712_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_lazyAssignment_713_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3, v_enabled_711_);
v___x_721_ = v_reuseFailAlloc_727_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 8, v___x_721_);
v___x_723_ = v___x_709_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_env_699_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_nextMacroScope_700_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_ngen_701_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_auxDeclNGen_702_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_traceState_703_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v_cache_704_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_recordedDeps_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v_messages_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 8, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_726_, 9, v_snapshotTasks_707_);
v___x_723_ = v_reuseFailAlloc_726_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_st_ref_put(v___y_690_, v___x_723_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_718_);
return v___x_725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_730_, v___y_731_);
lean_dec(v___y_731_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(32u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_737_ = ((size_t)5ULL);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_unsigned_to_nat(32u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_742_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v___x_738_);
lean_ctor_set(v___x_742_, 3, v___x_738_);
lean_ctor_set_usize(v___x_742_, 4, v___x_737_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_t_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v_infoState_748_; uint8_t v_enabled_749_; 
v___x_747_ = lean_st_ref_get(v___y_745_);
v_infoState_748_ = lean_ctor_get(v___x_747_, 8);
lean_inc_ref(v_infoState_748_);
lean_dec(v___x_747_);
v_enabled_749_ = lean_ctor_get_uint8(v_infoState_748_, sizeof(void*)*3);
lean_dec_ref(v_infoState_748_);
if (v_enabled_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v_t_743_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v_t_743_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_753_, v___y_745_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_t_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v_t_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(lean_object* v_stx_760_, lean_object* v_n_761_, lean_object* v_expectedType_x3f_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_n_761_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_stx_760_);
v___x_770_ = l_Lean_LocalContext_empty;
v___x_771_ = 0;
v___x_772_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_772_, 0, v___x_769_);
lean_ctor_set(v___x_772_, 1, v___x_770_);
lean_ctor_set(v___x_772_, 2, v_expectedType_x3f_762_);
lean_ctor_set(v___x_772_, 3, v_a_767_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*4, v___x_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*4 + 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_773_, v___y_763_, v___y_764_);
return v___x_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_expectedType_x3f_762_);
lean_dec(v_stx_760_);
v_a_775_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_766_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_766_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_783_, lean_object* v_n_784_, lean_object* v_expectedType_x3f_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v_stx_783_, v_n_784_, v_expectedType_x3f_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(lean_object* v_info_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_794_, 0, v_info_790_);
v___x_795_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_794_, v___y_791_, v___y_792_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0___boxed(lean_object* v_info_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v_info_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v_key_804_; lean_object* v_value_805_; lean_object* v_tail_806_; uint8_t v___x_807_; 
v_key_804_ = lean_ctor_get(v_x_802_, 0);
v_value_805_ = lean_ctor_get(v_x_802_, 1);
v_tail_806_ = lean_ctor_get(v_x_802_, 2);
v___x_807_ = lean_name_eq(v_key_804_, v_a_801_);
if (v___x_807_ == 0)
{
v_x_802_ = v_tail_806_;
goto _start;
}
else
{
lean_object* v___x_809_; 
lean_inc(v_value_805_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_value_805_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_810_, lean_object* v_x_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_810_, v_x_811_);
lean_dec(v_x_811_);
lean_dec(v_a_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_buckets_815_; lean_object* v___x_816_; uint64_t v___y_818_; 
v_buckets_815_ = lean_ctor_get(v_m_813_, 1);
v___x_816_ = lean_array_get_size(v_buckets_815_);
if (lean_obj_tag(v_a_814_) == 0)
{
uint64_t v___x_832_; 
v___x_832_ = 1723ULL;
v___y_818_ = v___x_832_;
goto v___jp_817_;
}
else
{
uint64_t v_hash_833_; 
v_hash_833_ = lean_ctor_get_uint64(v_a_814_, sizeof(void*)*2);
v___y_818_ = v_hash_833_;
goto v___jp_817_;
}
v___jp_817_:
{
uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v_fold_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_819_ = 32ULL;
v___x_820_ = lean_uint64_shift_right(v___y_818_, v___x_819_);
v_fold_821_ = lean_uint64_xor(v___y_818_, v___x_820_);
v___x_822_ = 16ULL;
v___x_823_ = lean_uint64_shift_right(v_fold_821_, v___x_822_);
v___x_824_ = lean_uint64_xor(v_fold_821_, v___x_823_);
v___x_825_ = lean_uint64_to_usize(v___x_824_);
v___x_826_ = lean_usize_of_nat(v___x_816_);
v___x_827_ = ((size_t)1ULL);
v___x_828_ = lean_usize_sub(v___x_826_, v___x_827_);
v___x_829_ = lean_usize_land(v___x_825_, v___x_828_);
v___x_830_ = lean_array_uget_borrowed(v_buckets_815_, v___x_829_);
v___x_831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_814_, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_m_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_m_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___lam__0(lean_object* v___x_837_, lean_object* v_entry_838_, lean_object* v_s_839_){
_start:
{
lean_object* v_addEntryFn_840_; lean_object* v_importedEntries_841_; lean_object* v_state_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_addEntryFn_840_ = lean_ctor_get(v___x_837_, 3);
lean_inc(v_addEntryFn_840_);
lean_dec_ref(v___x_837_);
v_importedEntries_841_ = lean_ctor_get(v_s_839_, 0);
v_state_842_ = lean_ctor_get(v_s_839_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_s_839_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v_s_839_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_state_842_);
lean_inc(v_importedEntries_841_);
lean_dec(v_s_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_state_846_; lean_object* v___x_848_; 
v_state_846_ = lean_apply_2(v_addEntryFn_840_, v_state_842_, v_entry_838_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_state_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_importedEntries_841_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_state_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_keys_851_, lean_object* v_i_852_, lean_object* v_k_853_){
_start:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_get_size(v_keys_851_);
v___x_855_ = lean_nat_dec_lt(v_i_852_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec(v_i_852_);
return v___x_855_;
}
else
{
lean_object* v_k_x27_856_; uint8_t v___x_857_; 
v_k_x27_856_ = lean_array_fget_borrowed(v_keys_851_, v_i_852_);
v___x_857_ = l_Lean_instBEqExtraModUse_beq(v_k_853_, v_k_x27_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_i_852_, v___x_858_);
lean_dec(v_i_852_);
v_i_852_ = v___x_859_;
goto _start;
}
else
{
lean_dec(v_i_852_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_keys_861_, lean_object* v_i_862_, lean_object* v_k_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_861_, v_i_862_, v_k_863_);
lean_dec_ref(v_k_863_);
lean_dec_ref(v_keys_861_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_866_, size_t v_x_867_, lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v_es_869_; lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v_j_873_; lean_object* v___x_874_; 
v_es_869_ = lean_ctor_get(v_x_866_, 0);
v___x_870_ = lean_box(2);
v___x_871_ = ((size_t)31ULL);
v___x_872_ = lean_usize_land(v_x_867_, v___x_871_);
v_j_873_ = lean_usize_to_nat(v___x_872_);
v___x_874_ = lean_array_get_borrowed(v___x_870_, v_es_869_, v_j_873_);
lean_dec(v_j_873_);
switch(lean_obj_tag(v___x_874_))
{
case 0:
{
lean_object* v_key_875_; uint8_t v___x_876_; 
v_key_875_ = lean_ctor_get(v___x_874_, 0);
v___x_876_ = l_Lean_instBEqExtraModUse_beq(v_x_868_, v_key_875_);
return v___x_876_;
}
case 1:
{
lean_object* v_node_877_; size_t v___x_878_; size_t v___x_879_; 
v_node_877_ = lean_ctor_get(v___x_874_, 0);
v___x_878_ = ((size_t)5ULL);
v___x_879_ = lean_usize_shift_right(v_x_867_, v___x_878_);
v_x_866_ = v_node_877_;
v_x_867_ = v___x_879_;
goto _start;
}
default: 
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
}
}
else
{
lean_object* v_ks_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_ks_882_ = lean_ctor_get(v_x_866_, 0);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_ks_882_, v___x_883_, v_x_868_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v_x_8325__boxed_888_; uint8_t v_res_889_; lean_object* v_r_890_; 
v_x_8325__boxed_888_ = lean_unbox_usize(v_x_886_);
lean_dec(v_x_886_);
v_res_889_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_885_, v_x_8325__boxed_888_, v_x_887_);
lean_dec_ref(v_x_887_);
lean_dec_ref(v_x_885_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
uint64_t v___x_893_; size_t v___x_894_; uint8_t v___x_895_; 
v___x_893_ = l_Lean_instHashableExtraModUse_hash(v_x_892_);
v___x_894_ = lean_uint64_to_usize(v___x_893_);
v___x_895_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_891_, v___x_894_, v_x_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_896_, v_x_897_);
lean_dec_ref(v_x_897_);
lean_dec_ref(v_x_896_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_900_; double v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_float_of_nat(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_cls_905_, lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_ref_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_957_; 
v_ref_910_ = lean_ctor_get(v___y_907_, 2);
v___x_911_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_906_, v___y_907_, v___y_908_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_957_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_957_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_957_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v_traceState_917_; lean_object* v_env_918_; lean_object* v_nextMacroScope_919_; lean_object* v_ngen_920_; lean_object* v_auxDeclNGen_921_; lean_object* v_cache_922_; lean_object* v_recordedDeps_923_; lean_object* v_messages_924_; lean_object* v_infoState_925_; lean_object* v_snapshotTasks_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_956_; 
v___x_916_ = lean_st_ref_take(v___y_908_);
v_traceState_917_ = lean_ctor_get(v___x_916_, 4);
v_env_918_ = lean_ctor_get(v___x_916_, 0);
v_nextMacroScope_919_ = lean_ctor_get(v___x_916_, 1);
v_ngen_920_ = lean_ctor_get(v___x_916_, 2);
v_auxDeclNGen_921_ = lean_ctor_get(v___x_916_, 3);
v_cache_922_ = lean_ctor_get(v___x_916_, 5);
v_recordedDeps_923_ = lean_ctor_get(v___x_916_, 6);
v_messages_924_ = lean_ctor_get(v___x_916_, 7);
v_infoState_925_ = lean_ctor_get(v___x_916_, 8);
v_snapshotTasks_926_ = lean_ctor_get(v___x_916_, 9);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_956_ == 0)
{
v___x_928_ = v___x_916_;
v_isShared_929_ = v_isSharedCheck_956_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snapshotTasks_926_);
lean_inc(v_infoState_925_);
lean_inc(v_messages_924_);
lean_inc(v_recordedDeps_923_);
lean_inc(v_cache_922_);
lean_inc(v_traceState_917_);
lean_inc(v_auxDeclNGen_921_);
lean_inc(v_ngen_920_);
lean_inc(v_nextMacroScope_919_);
lean_inc(v_env_918_);
lean_dec(v___x_916_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_956_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint64_t v_tid_930_; lean_object* v_traces_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_955_; 
v_tid_930_ = lean_ctor_get_uint64(v_traceState_917_, sizeof(void*)*1);
v_traces_931_ = lean_ctor_get(v_traceState_917_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_traceState_917_);
if (v_isSharedCheck_955_ == 0)
{
v___x_933_ = v_traceState_917_;
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_traces_931_);
lean_dec(v_traceState_917_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; double v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_935_ = lean_box(0);
v___x_936_ = lean_box(0);
v___x_937_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_938_ = 0;
v___x_939_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_940_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_940_, 0, v_cls_905_);
lean_ctor_set(v___x_940_, 1, v___x_936_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3, v___x_937_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3 + 8, v___x_937_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 16, v___x_938_);
v___x_941_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_942_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v_a_912_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_inc(v_ref_910_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_ref_910_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_PersistentArray_push___redArg(v_traces_931_, v___x_943_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_944_);
v___x_946_ = v___x_933_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_944_);
lean_ctor_set_uint64(v_reuseFailAlloc_954_, sizeof(void*)*1, v_tid_930_);
v___x_946_ = v_reuseFailAlloc_954_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 4, v___x_946_);
v___x_948_ = v___x_928_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_env_918_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_nextMacroScope_919_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_ngen_920_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_auxDeclNGen_921_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v_recordedDeps_923_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_messages_924_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v_infoState_925_);
lean_ctor_set(v_reuseFailAlloc_953_, 9, v_snapshotTasks_926_);
v___x_948_ = v_reuseFailAlloc_953_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_st_ref_put(v___y_908_, v___x_948_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_935_);
v___x_951_ = v___x_914_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_935_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_cls_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_958_, v_msg_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_963_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_968_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v_cls_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_cls_983_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_984_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_985_ = l_Lean_Name_append(v___x_984_, v_cls_983_);
return v___x_985_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_mod_996_, uint8_t v_isMeta_997_, lean_object* v_hint_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_env_1020_; uint8_t v_isExporting_1021_; lean_object* v_entry_1022_; lean_object* v___x_1023_; lean_object* v_env_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1018_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_1019_ = lean_st_ref_get(v___y_1000_);
v_env_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_env_1020_);
lean_dec(v___x_1019_);
v_isExporting_1021_ = lean_ctor_get_uint8(v_env_1020_, sizeof(void*)*13);
lean_dec_ref(v_env_1020_);
lean_inc(v_mod_996_);
v_entry_1022_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1022_, 0, v_mod_996_);
lean_ctor_set_uint8(v_entry_1022_, sizeof(void*)*1, v_isExporting_1021_);
lean_ctor_set_uint8(v_entry_1022_, sizeof(void*)*1 + 1, v_isMeta_997_);
v___x_1023_ = lean_st_ref_get(v___y_1000_);
v_env_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_env_1024_);
lean_dec(v___x_1023_);
v___x_1025_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1026_ = lean_box(1);
v___x_1027_ = lean_box(0);
v___x_1028_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1018_, v___x_1025_, v_env_1024_, v___x_1026_, v___x_1027_);
v___x_1029_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v___x_1028_, v_entry_1022_);
lean_dec(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v_toCold_1030_; lean_object* v_options_1031_; lean_object* v_inheritedTraceOptions_1032_; uint8_t v_hasTrace_1033_; lean_object* v___f_1034_; uint8_t v___x_1035_; lean_object* v___y_1037_; 
v_toCold_1030_ = lean_ctor_get(v___y_999_, 0);
v_options_1031_ = lean_ctor_get(v_toCold_1030_, 2);
v_inheritedTraceOptions_1032_ = lean_ctor_get(v_toCold_1030_, 11);
v_hasTrace_1033_ = lean_ctor_get_uint8(v_options_1031_, sizeof(void*)*1);
v___f_1034_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_1034_, 0, v___x_1025_);
lean_closure_set(v___f_1034_, 1, v_entry_1022_);
v___x_1035_ = 1;
if (v_hasTrace_1033_ == 0)
{
lean_dec(v_hint_998_);
lean_dec(v_mod_996_);
v___y_1037_ = v___y_1000_;
goto v___jp_1036_;
}
else
{
lean_object* v_cls_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_cls_1055_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_1075_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12);
v___x_1076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1032_, v_options_1031_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_hint_998_);
lean_dec(v_mod_996_);
v___y_1037_ = v___y_1000_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1077_; lean_object* v___y_1079_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14);
if (v_isExporting_1021_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19));
v___y_1079_ = v___x_1086_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20));
v___y_1079_ = v___x_1087_;
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_inc_ref(v___y_1079_);
v___x_1080_ = l_Lean_stringToMessageData(v___y_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1077_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
if (v_isMeta_997_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17));
v___y_1062_ = v___x_1083_;
v___y_1063_ = v___x_1084_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18));
v___y_1062_ = v___x_1083_;
v___y_1063_ = v___x_1085_;
goto v___jp_1061_;
}
}
}
v___jp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1057_);
lean_ctor_set(v___x_1059_, 1, v___y_1058_);
v___x_1060_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_1055_, v___x_1059_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_dec_ref_known(v___x_1060_, 1);
v___y_1037_ = v___y_1000_;
goto v___jp_1036_;
}
else
{
lean_dec_ref(v___f_1034_);
return v___x_1060_;
}
}
v___jp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
lean_inc_ref(v___y_1063_);
v___x_1064_ = l_Lean_stringToMessageData(v___y_1063_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___y_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_MessageData_ofName(v_mod_996_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_Name_isAnonymous(v_hint_998_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8);
v___x_1072_ = l_Lean_MessageData_ofName(v_hint_998_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___y_1057_ = v___x_1069_;
v___y_1058_ = v___x_1073_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1074_; 
lean_dec(v_hint_998_);
v___x_1074_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9);
v___y_1057_ = v___x_1069_;
v___y_1058_ = v___x_1074_;
goto v___jp_1056_;
}
}
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v_toEnvExtension_1039_; lean_object* v_env_1040_; lean_object* v_nextMacroScope_1041_; lean_object* v_ngen_1042_; lean_object* v_auxDeclNGen_1043_; lean_object* v_traceState_1044_; lean_object* v_recordedDeps_1045_; lean_object* v_messages_1046_; lean_object* v_infoState_1047_; lean_object* v_snapshotTasks_1048_; lean_object* v_asyncMode_1049_; uint8_t v_logWrites_1050_; lean_object* v___x_1051_; 
v___x_1038_ = lean_st_ref_take(v___y_1037_);
v_toEnvExtension_1039_ = lean_ctor_get(v___x_1025_, 0);
v_env_1040_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_env_1040_);
v_nextMacroScope_1041_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_nextMacroScope_1041_);
v_ngen_1042_ = lean_ctor_get(v___x_1038_, 2);
lean_inc_ref(v_ngen_1042_);
v_auxDeclNGen_1043_ = lean_ctor_get(v___x_1038_, 3);
lean_inc_ref(v_auxDeclNGen_1043_);
v_traceState_1044_ = lean_ctor_get(v___x_1038_, 4);
lean_inc_ref(v_traceState_1044_);
v_recordedDeps_1045_ = lean_ctor_get(v___x_1038_, 6);
lean_inc_ref(v_recordedDeps_1045_);
v_messages_1046_ = lean_ctor_get(v___x_1038_, 7);
lean_inc_ref(v_messages_1046_);
v_infoState_1047_ = lean_ctor_get(v___x_1038_, 8);
lean_inc_ref(v_infoState_1047_);
v_snapshotTasks_1048_ = lean_ctor_get(v___x_1038_, 9);
lean_inc_ref(v_snapshotTasks_1048_);
lean_dec(v___x_1038_);
v_asyncMode_1049_ = lean_ctor_get(v_toEnvExtension_1039_, 2);
v_logWrites_1050_ = lean_ctor_get_uint8(v_toEnvExtension_1039_, sizeof(void*)*6);
v___x_1051_ = lean_box(0);
if (v_logWrites_1050_ == 0)
{
lean_object* v___x_1052_; 
lean_inc_ref(v_toEnvExtension_1039_);
v___x_1052_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1039_, v_env_1040_, v___f_1034_, v_asyncMode_1049_, v___x_1027_, v___x_1035_);
v___y_1003_ = v___y_1037_;
v___y_1004_ = v_ngen_1042_;
v___y_1005_ = v___x_1051_;
v___y_1006_ = v_traceState_1044_;
v___y_1007_ = v_messages_1046_;
v___y_1008_ = v_auxDeclNGen_1043_;
v___y_1009_ = v_nextMacroScope_1041_;
v___y_1010_ = v_recordedDeps_1045_;
v___y_1011_ = v_snapshotTasks_1048_;
v___y_1012_ = v_infoState_1047_;
v___y_1013_ = v___x_1052_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_inc_ref_n(v_toEnvExtension_1039_, 2);
v___x_1053_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1039_, v_env_1040_);
lean_dec_ref(v_env_1040_);
v___x_1054_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1039_, v___x_1053_, v___f_1034_, v_asyncMode_1049_, v___x_1027_, v___x_1035_);
v___y_1003_ = v___y_1037_;
v___y_1004_ = v_ngen_1042_;
v___y_1005_ = v___x_1051_;
v___y_1006_ = v_traceState_1044_;
v___y_1007_ = v_messages_1046_;
v___y_1008_ = v_auxDeclNGen_1043_;
v___y_1009_ = v_nextMacroScope_1041_;
v___y_1010_ = v_recordedDeps_1045_;
v___y_1011_ = v_snapshotTasks_1048_;
v___y_1012_ = v_infoState_1047_;
v___y_1013_ = v___x_1054_;
goto v___jp_1002_;
}
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref_known(v_entry_1022_, 1);
lean_dec(v_hint_998_);
lean_dec(v_mod_996_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
v___jp_1002_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_1015_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1015_, 0, v___y_1013_);
lean_ctor_set(v___x_1015_, 1, v___y_1009_);
lean_ctor_set(v___x_1015_, 2, v___y_1004_);
lean_ctor_set(v___x_1015_, 3, v___y_1008_);
lean_ctor_set(v___x_1015_, 4, v___y_1006_);
lean_ctor_set(v___x_1015_, 5, v___x_1014_);
lean_ctor_set(v___x_1015_, 6, v___y_1010_);
lean_ctor_set(v___x_1015_, 7, v___y_1007_);
lean_ctor_set(v___x_1015_, 8, v___y_1012_);
lean_ctor_set(v___x_1015_, 9, v___y_1011_);
v___x_1016_ = lean_st_ref_put(v___y_1003_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___y_1005_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_mod_1090_, lean_object* v_isMeta_1091_, lean_object* v_hint_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_isMeta_boxed_1096_; lean_object* v_res_1097_; 
v_isMeta_boxed_1096_ = lean_unbox(v_isMeta_1091_);
v_res_1097_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_mod_1090_, v_isMeta_boxed_1096_, v_hint_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object* v___x_1098_, lean_object* v_declName_1099_, lean_object* v_as_1100_, size_t v_sz_1101_, size_t v_i_1102_, lean_object* v_b_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_usize_dec_lt(v_i_1102_, v_sz_1101_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_declName_1099_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_b_1103_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v_modules_1110_; lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v_toImport_1114_; lean_object* v_module_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1109_ = l_Lean_Environment_header(v___x_1098_);
v_modules_1110_ = lean_ctor_get(v___x_1109_, 3);
lean_inc_ref(v_modules_1110_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1112_ = lean_array_uget_borrowed(v_as_1100_, v_i_1102_);
v___x_1113_ = lean_array_get(v___x_1111_, v_modules_1110_, v_a_1112_);
lean_dec_ref(v_modules_1110_);
v_toImport_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_toImport_1114_);
lean_dec(v___x_1113_);
v_module_1115_ = lean_ctor_get(v_toImport_1114_, 0);
lean_inc(v_module_1115_);
lean_dec_ref(v_toImport_1114_);
v___x_1116_ = lean_box(0);
v___x_1117_ = 0;
lean_inc(v_declName_1099_);
v___x_1118_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1115_, v___x_1117_, v_declName_1099_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1118_) == 0)
{
size_t v___x_1119_; size_t v___x_1120_; 
lean_dec_ref_known(v___x_1118_, 1);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1102_, v___x_1119_);
v_i_1102_ = v___x_1120_;
v_b_1103_ = v___x_1116_;
goto _start;
}
else
{
lean_dec(v_declName_1099_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v___x_1122_, lean_object* v_declName_1123_, lean_object* v_as_1124_, lean_object* v_sz_1125_, lean_object* v_i_1126_, lean_object* v_b_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_sz_boxed_1131_; size_t v_i_boxed_1132_; lean_object* v_res_1133_; 
v_sz_boxed_1131_ = lean_unbox_usize(v_sz_1125_);
lean_dec(v_sz_1125_);
v_i_boxed_1132_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v___x_1122_, v_declName_1123_, v_as_1124_, v_sz_boxed_1131_, v_i_boxed_1132_, v_b_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_as_1124_);
lean_dec_ref(v___x_1122_);
return v_res_1133_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(lean_object* v_declName_1137_, uint8_t v_isMeta_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_env_1147_; lean_object* v___y_1149_; lean_object* v___x_1162_; 
v___x_1142_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0);
v___x_1143_ = lean_st_ref_get(v___y_1140_);
v_env_1147_ = lean_ctor_get(v___x_1143_, 0);
lean_inc_ref(v_env_1147_);
lean_dec(v___x_1143_);
v___x_1162_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1147_, v_declName_1137_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1137_);
goto v___jp_1144_;
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1164_; lean_object* v_modules_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Environment_header(v_env_1147_);
v_modules_1165_ = lean_ctor_get(v___x_1164_, 3);
lean_inc_ref(v_modules_1165_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = lean_array_get_size(v_modules_1165_);
v___x_1167_ = lean_nat_dec_lt(v_val_1163_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v_modules_1165_);
lean_dec(v_val_1163_);
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1137_);
goto v___jp_1144_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___y_1171_; 
v___x_1168_ = lean_array_fget(v_modules_1165_, v_val_1163_);
lean_dec(v_val_1163_);
lean_dec_ref(v_modules_1165_);
v___x_1169_ = lean_st_ref_get(v___y_1140_);
if (v_isMeta_1138_ == 0)
{
lean_dec(v___x_1169_);
v___y_1171_ = v_isMeta_1138_;
goto v___jp_1170_;
}
else
{
lean_object* v_env_1182_; uint8_t v___x_1183_; 
v_env_1182_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1169_);
lean_inc(v_declName_1137_);
v___x_1183_ = l_Lean_isMarkedMeta(v_env_1182_, v_declName_1137_);
if (v___x_1183_ == 0)
{
v___y_1171_ = v_isMeta_1138_;
goto v___jp_1170_;
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
v___y_1171_ = v___x_1184_;
goto v___jp_1170_;
}
}
v___jp_1170_:
{
lean_object* v_toImport_1172_; lean_object* v_module_1173_; lean_object* v___x_1174_; 
v_toImport_1172_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_toImport_1172_);
lean_dec(v___x_1168_);
v_module_1173_ = lean_ctor_get(v_toImport_1172_, 0);
lean_inc(v_module_1173_);
lean_dec_ref(v_toImport_1172_);
lean_inc(v_declName_1137_);
v___x_1174_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1173_, v___y_1171_, v_declName_1137_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref_known(v___x_1174_, 1);
v___x_1175_ = l_Lean_indirectModUseExt;
v___x_1176_ = lean_box(1);
v___x_1177_ = lean_box(0);
lean_inc_ref(v_env_1147_);
v___x_1178_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1142_, v___x_1175_, v_env_1147_, v___x_1176_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v___x_1178_, v_declName_1137_);
lean_dec(v___x_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1));
v___y_1149_ = v___x_1180_;
goto v___jp_1148_;
}
else
{
lean_object* v_val_1181_; 
v_val_1181_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v___x_1179_, 1);
v___y_1149_ = v_val_1181_;
goto v___jp_1148_;
}
}
else
{
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1137_);
return v___x_1174_;
}
}
}
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
v___jp_1148_:
{
lean_object* v___x_1150_; size_t v_sz_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_box(0);
v_sz_1151_ = lean_array_size(v___y_1149_);
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v_env_1147_, v_declName_1137_, v___y_1149_, v_sz_1151_, v___x_1152_, v___x_1150_, v___y_1139_, v___y_1140_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_env_1147_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1161_);
v___x_1155_ = v___x_1153_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v___x_1153_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1150_);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1150_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1185_, lean_object* v_isMeta_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_isMeta_boxed_1190_; lean_object* v_res_1191_; 
v_isMeta_boxed_1190_ = lean_unbox(v_isMeta_1186_);
v_res_1191_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_declName_1185_, v_isMeta_boxed_1190_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1191_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1200_ = lean_box(1);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_1202_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
lean_ctor_set(v___x_1203_, 2, v___x_1200_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_x_1204_, lean_object* v_stx_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1292_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1292_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1292_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_infoState_1216_; uint8_t v_enabled_1217_; 
v___x_1214_ = l_Lean_Syntax_getId(v_a_1210_);
v___x_1215_ = lean_st_ref_get(v___y_1207_);
v_infoState_1216_ = lean_ctor_get(v___x_1215_, 8);
lean_inc_ref(v_infoState_1216_);
lean_dec(v___x_1215_);
v_enabled_1217_ = lean_ctor_get_uint8(v_infoState_1216_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1216_);
if (v_enabled_1217_ == 0)
{
lean_object* v___x_1219_; 
lean_dec(v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1219_ = v___x_1212_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
else
{
uint8_t v___x_1221_; 
v___x_1221_ = l_Lean_Name_isAtomic(v___x_1214_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = l_Lean_Name_getRoot(v___x_1214_);
v___x_1223_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1224_ = lean_name_eq(v___x_1222_, v___x_1223_);
lean_dec(v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1226_; 
lean_dec(v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1226_ = v___x_1212_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1214_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___y_1231_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1212_);
v___x_1228_ = lean_box(0);
lean_inc(v___x_1214_);
v___x_1229_ = l_Lean_Name_replacePrefix(v___x_1214_, v___x_1223_, v___x_1228_);
v___x_1286_ = lean_box(0);
v___x_1287_ = l_Lean_Syntax_identComponents(v_a_1210_, v___x_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
v___y_1231_ = v___x_1287_;
goto v___jp_1230_;
}
else
{
lean_object* v_tail_1288_; 
v_tail_1288_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_tail_1288_);
lean_dec_ref_known(v___x_1287_, 2);
v___y_1231_ = v_tail_1288_;
goto v___jp_1230_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1232_ = lean_array_mk(v___y_1231_);
v___x_1233_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1234_ = lean_box(2);
v___x_1235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___x_1233_);
lean_ctor_set(v___x_1235_, 2, v___x_1232_);
lean_inc_n(v___x_1229_, 2);
v___x_1236_ = l_Lean_mkIdentFrom(v___x_1235_, v___x_1229_, v_enabled_1217_);
lean_dec_ref_known(v___x_1235_, 3);
v___x_1237_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1238_ = lean_box(0);
lean_inc(v___x_1236_);
v___x_1239_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1229_);
lean_ctor_set(v___x_1239_, 2, v___x_1237_);
lean_ctor_set(v___x_1239_, 3, v___x_1238_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*4, v___x_1221_);
v___x_1240_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v___x_1239_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1276_; 
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1277_);
v___x_1242_ = v___x_1240_;
v_isShared_1243_ = v_isSharedCheck_1276_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v___x_1240_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1276_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v_env_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_st_ref_get(v___y_1207_);
v_env_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_env_1245_);
lean_dec(v___x_1244_);
lean_inc(v___x_1229_);
v___x_1246_ = l_Lean_Environment_contains(v_env_1245_, v___x_1229_, v_enabled_1217_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1248_; 
lean_dec(v___x_1236_);
lean_dec(v___x_1229_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1214_);
v___x_1248_ = v___x_1242_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1214_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
else
{
lean_object* v___x_1250_; 
lean_del_object(v___x_1242_);
lean_inc(v___x_1229_);
v___x_1250_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v___x_1229_, v___x_1221_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref_known(v___x_1250_, 1);
v___x_1251_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v___x_1236_, v___x_1229_, v___x_1238_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1259_);
v___x_1253_ = v___x_1251_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1251_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1214_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1214_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v___x_1214_);
v_a_1260_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1251_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1251_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
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
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___x_1236_);
lean_dec(v___x_1229_);
lean_dec(v___x_1214_);
v_a_1268_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1250_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1250_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v___x_1236_);
lean_dec(v___x_1229_);
lean_dec(v___x_1214_);
v_a_1278_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1240_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1240_);
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
}
}
else
{
lean_object* v___x_1290_; 
lean_dec(v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1290_ = v___x_1212_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1214_);
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
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1209_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1209_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_x_1301_, lean_object* v_stx_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v_x_8886__boxed_1306_; lean_object* v_res_1307_; 
v_x_8886__boxed_1306_ = lean_unbox(v_x_1301_);
v_res_1307_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_x_8886__boxed_1306_, v_stx_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1341_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1342_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1340_, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_t_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_1345_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_t_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_t_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1355_, lean_object* v_m_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_1356_, v_a_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1359_, lean_object* v_m_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1359_, v_m_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_m_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_1364_, v_x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_res_1370_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_1367_, v_x_1368_, v_x_1369_);
lean_dec_ref(v_x_1369_);
lean_dec_ref(v_x_1368_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1372_, lean_object* v_a_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_1373_, v_x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1376_, lean_object* v_a_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_00_u03b2_1376_, v_a_1377_, v_x_1378_);
lean_dec(v_x_1378_);
lean_dec(v_a_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, size_t v_x_1382_, lean_object* v_x_1383_){
_start:
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_1381_, v_x_1382_, v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
size_t v_x_9221__boxed_1389_; uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_x_9221__boxed_1389_ = lean_unbox_usize(v_x_1387_);
lean_dec(v_x_1387_);
v_res_1390_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1385_, v_x_1386_, v_x_9221__boxed_1389_, v_x_1388_);
lean_dec_ref(v_x_1388_);
lean_dec_ref(v_x_1386_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object* v_00_u03b1_1392_, lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(v_00_u03b1_1398_, v_constName_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1404_, lean_object* v_keys_1405_, lean_object* v_vals_1406_, lean_object* v_heq_1407_, lean_object* v_i_1408_, lean_object* v_k_1409_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_1405_, v_i_1408_, v_k_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1411_, lean_object* v_keys_1412_, lean_object* v_vals_1413_, lean_object* v_heq_1414_, lean_object* v_i_1415_, lean_object* v_k_1416_){
_start:
{
uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_res_1417_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(v_00_u03b2_1411_, v_keys_1412_, v_vals_1413_, v_heq_1414_, v_i_1415_, v_k_1416_);
lean_dec_ref(v_k_1416_);
lean_dec_ref(v_vals_1413_);
lean_dec_ref(v_keys_1412_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object* v_00_u03b1_1419_, lean_object* v_ref_1420_, lean_object* v_constName_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_1420_, v_constName_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_1426_, v_ref_1427_, v_constName_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_ref_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1433_, lean_object* v_ref_1434_, lean_object* v_msg_1435_, lean_object* v_declHint_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_1434_, v_msg_1435_, v_declHint_1436_, v___y_1437_, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1441_, lean_object* v_ref_1442_, lean_object* v_msg_1443_, lean_object* v_declHint_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(v_00_u03b1_1441_, v_ref_1442_, v_msg_1443_, v_declHint_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v_ref_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1449_, lean_object* v_declHint_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1449_, v_declHint_1450_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1455_, lean_object* v_declHint_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(v_msg_1455_, v_declHint_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1461_, lean_object* v_ref_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_1462_, v_msg_1463_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_ref_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_1468_, v_ref_1469_, v_msg_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_ref_1469_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1476_, v___y_1477_, v___y_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1481_, v_msg_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1490_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1491_ = l_Lean_addBuiltinDocString(v___x_1489_, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1521_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1522_ = l_Lean_addBuiltinDeclarationRanges(v___x_1520_, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1553_, uint8_t v___x_1554_, lean_object* v_id_1555_, lean_object* v_x_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1560_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1553_, v___x_1554_);
v___x_1561_ = lean_string_append(v___x_1559_, v___x_1560_);
lean_dec_ref(v___x_1560_);
v___x_1562_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
v___x_1564_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1555_, v___x_1563_, v___y_1557_, v___y_1558_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v_id_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v___x_2296__boxed_1571_; lean_object* v_res_1572_; 
v___x_2296__boxed_1571_ = lean_unbox(v___x_1566_);
v_res_1572_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1565_, v___x_2296__boxed_1571_, v_id_1567_, v_x_1568_, v___y_1569_, v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v_x_1568_);
lean_dec(v_id_1567_);
return v_res_1572_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1583_ = l_String_toRawSubstring_x27(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___y_1588_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1584_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_x_1584_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v_x_1584_);
v___x_1609_ = lean_box(1);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1586_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v_id_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1611_ = lean_unsigned_to_nat(1u);
v_id_1612_ = l_Lean_Syntax_getArg(v_x_1584_, v___x_1611_);
lean_dec(v_x_1584_);
v___x_1613_ = l_Lean_TSyntax_getId(v_id_1612_);
lean_inc(v___x_1613_);
v___x_1614_ = l_Lean_Macro_resolveGlobalName(v___x_1613_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
if (lean_obj_tag(v_a_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_a_1616_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1614_, 2);
v___x_1617_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1618_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1613_, v___x_1608_);
v___x_1619_ = lean_string_append(v___x_1617_, v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
v___x_1622_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1612_, v___x_1621_, v_a_1585_, v_a_1616_);
lean_dec(v_id_1612_);
v___y_1588_ = v___x_1622_;
goto v___jp_1587_;
}
else
{
lean_object* v_head_1623_; lean_object* v_snd_1624_; 
v_head_1623_ = lean_ctor_get(v_a_1615_, 0);
v_snd_1624_ = lean_ctor_get(v_head_1623_, 1);
if (lean_obj_tag(v_snd_1624_) == 0)
{
lean_object* v_tail_1625_; 
v_tail_1625_ = lean_ctor_get(v_a_1615_, 1);
if (lean_obj_tag(v_tail_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1651_; 
lean_inc(v_head_1623_);
lean_dec(v___x_1613_);
v_a_1626_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1652_);
v___x_1628_ = v___x_1614_;
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1614_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1651_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_fst_1630_; lean_object* v_quotContext_1631_; lean_object* v_currMacroScope_1632_; lean_object* v_ref_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_fst_1630_ = lean_ctor_get(v_head_1623_, 0);
lean_inc(v_fst_1630_);
lean_dec(v_head_1623_);
v_quotContext_1631_ = lean_ctor_get(v_a_1585_, 1);
v_currMacroScope_1632_ = lean_ctor_get(v_a_1585_, 2);
v_ref_1633_ = lean_ctor_get(v_a_1585_, 5);
v___x_1634_ = 0;
v___x_1635_ = l_Lean_SourceInfo_fromRef(v_ref_1633_, v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1637_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1638_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1632_);
lean_inc(v_quotContext_1631_);
v___x_1639_ = l_Lean_addMacroScope(v_quotContext_1631_, v___x_1638_, v_currMacroScope_1632_);
v___x_1640_ = lean_box(0);
lean_inc_n(v___x_1635_, 2);
v___x_1641_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1635_);
lean_ctor_set(v___x_1641_, 1, v___x_1637_);
lean_ctor_set(v___x_1641_, 2, v___x_1639_);
lean_ctor_set(v___x_1641_, 3, v___x_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1643_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1644_ = l_Lean_Name_append(v___x_1643_, v_fst_1630_);
v___x_1645_ = l_Lean_mkIdentFrom(v_id_1612_, v___x_1644_, v___x_1608_);
lean_dec(v_id_1612_);
v___x_1646_ = l_Lean_Syntax_node1(v___x_1635_, v___x_1642_, v___x_1645_);
v___x_1647_ = l_Lean_Syntax_node2(v___x_1635_, v___x_1636_, v___x_1641_, v___x_1646_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1647_);
v___x_1649_ = v___x_1628_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_a_1626_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1654_; 
lean_inc_ref(v_a_1615_);
v_a_1653_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1614_, 2);
v___x_1654_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1613_, v___x_1608_, v_id_1612_, v_a_1615_, v_a_1585_, v_a_1653_);
lean_dec_ref_known(v_a_1615_, 2);
lean_dec(v_id_1612_);
v___y_1588_ = v___x_1654_;
goto v___jp_1587_;
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
lean_inc_ref(v_a_1615_);
v_a_1655_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1614_, 2);
v___x_1656_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1613_, v___x_1608_, v_id_1612_, v_a_1615_, v_a_1585_, v_a_1655_);
lean_dec_ref_known(v_a_1615_, 2);
lean_dec(v_id_1612_);
v___y_1588_ = v___x_1656_;
goto v___jp_1587_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v___x_1613_);
lean_dec(v_id_1612_);
v_a_1657_ = lean_ctor_get(v___x_1614_, 0);
v_a_1658_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1614_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_inc(v_a_1657_);
lean_dec(v___x_1614_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
v___jp_1587_:
{
if (lean_obj_tag(v___y_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1589_ = lean_ctor_get(v___y_1588_, 0);
v_a_1590_ = lean_ctor_get(v___y_1588_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___y_1588_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___y_1588_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
lean_dec(v___y_1588_);
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
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1598_; lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1598_ = lean_ctor_get(v___y_1588_, 0);
v_a_1599_ = lean_ctor_get(v___y_1588_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___y_1588_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___y_1588_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_inc(v_a_1598_);
lean_dec(v___y_1588_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1666_, v_a_1667_, v_a_1668_);
lean_dec_ref(v_a_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1670_){
_start:
{
lean_object* v_subExpr_1672_; lean_object* v_expr_1673_; lean_object* v___x_1674_; 
v_subExpr_1672_ = lean_ctor_get(v___y_1670_, 3);
v_expr_1673_ = lean_ctor_get(v_subExpr_1672_, 0);
lean_inc_ref(v_expr_1673_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_expr_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1675_);
lean_dec_ref(v___y_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1678_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1694_, lean_object* v_us_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1697_ = l_Lean_Name_append(v___x_1696_, v_c_1694_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1698_, lean_object* v_us_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1698_, v_us_1699_);
lean_dec(v_us_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1706_);
lean_dec(v_x_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1818_; 
v___x_1742_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1735_);
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1818_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1818_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
switch(lean_obj_tag(v_a_1743_))
{
case 0:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec_ref_known(v_a_1743_, 1);
v___x_1747_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1749_ = v___x_1745_;
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
case 1:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_dec_ref_known(v_a_1743_, 1);
v___x_1751_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1751_);
v___x_1753_ = v___x_1745_;
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
case 2:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref_known(v_a_1743_, 1);
v___x_1755_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1755_);
v___x_1757_ = v___x_1745_;
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
case 3:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec_ref_known(v_a_1743_, 1);
v___x_1759_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1759_);
v___x_1761_ = v___x_1745_;
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
case 4:
{
lean_object* v_declName_1763_; lean_object* v_us_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_declName_1763_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_declName_1763_);
v_us_1764_ = lean_ctor_get(v_a_1743_, 1);
lean_inc(v_us_1764_);
lean_dec_ref_known(v_a_1743_, 2);
v___x_1765_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1763_, v_us_1764_);
lean_dec(v_us_1764_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1765_);
v___x_1767_ = v___x_1745_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
case 5:
{
lean_object* v_fn_1769_; lean_object* v___x_1770_; 
v_fn_1769_ = lean_ctor_get(v_a_1743_, 0);
lean_inc_ref(v_fn_1769_);
lean_dec_ref_known(v_a_1743_, 2);
v___x_1770_ = l_Lean_Expr_getAppFn(v_fn_1769_);
lean_dec_ref(v_fn_1769_);
if (lean_obj_tag(v___x_1770_) == 4)
{
lean_object* v_declName_1771_; lean_object* v_us_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_declName_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_declName_1771_);
v_us_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc(v_us_1772_);
lean_dec_ref_known(v___x_1770_, 2);
v___x_1773_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1771_, v_us_1772_);
lean_dec(v_us_1772_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1773_);
v___x_1775_ = v___x_1745_;
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
else
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec_ref(v___x_1770_);
v___x_1777_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1777_);
v___x_1779_ = v___x_1745_;
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
}
case 6:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec_ref_known(v_a_1743_, 3);
v___x_1781_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1781_);
v___x_1783_ = v___x_1745_;
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
case 7:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec_ref_known(v_a_1743_, 3);
v___x_1785_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1785_);
v___x_1787_ = v___x_1745_;
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
case 8:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec_ref_known(v_a_1743_, 4);
v___x_1789_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1789_);
v___x_1791_ = v___x_1745_;
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
case 9:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec_ref_known(v_a_1743_, 1);
v___x_1793_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1793_);
v___x_1795_ = v___x_1745_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
case 10:
{
lean_object* v_data_1797_; 
v_data_1797_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_data_1797_);
lean_dec_ref_known(v_a_1743_, 2);
if (lean_obj_tag(v_data_1797_) == 1)
{
lean_object* v_tail_1798_; 
v_tail_1798_ = lean_ctor_get(v_data_1797_, 1);
if (lean_obj_tag(v_tail_1798_) == 0)
{
lean_object* v_head_1799_; lean_object* v_fst_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_head_1799_ = lean_ctor_get(v_data_1797_, 0);
lean_inc(v_head_1799_);
lean_dec_ref_known(v_data_1797_, 2);
v_fst_1800_ = lean_ctor_get(v_head_1799_, 0);
lean_inc(v_fst_1800_);
lean_dec(v_head_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1802_ = l_Lean_Name_append(v___x_1801_, v_fst_1800_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1802_);
v___x_1804_ = v___x_1745_;
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
else
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1797_);
lean_dec_ref_known(v_data_1797_, 2);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1806_);
v___x_1808_ = v___x_1745_;
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
else
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1797_);
lean_dec(v_data_1797_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1810_);
v___x_1812_ = v___x_1745_;
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
default: 
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec_ref_known(v_a_1743_, 3);
v___x_1814_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1814_);
v___x_1816_ = v___x_1745_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1827_, lean_object* v_k_1828_, lean_object* v_v_1829_){
_start:
{
lean_object* v_map_1830_; uint8_t v_hasTrace_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1844_; 
v_map_1830_ = lean_ctor_get(v_o_1827_, 0);
v_hasTrace_1831_ = lean_ctor_get_uint8(v_o_1827_, sizeof(void*)*1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_o_1827_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1833_ = v_o_1827_;
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_map_1830_);
lean_dec(v_o_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1844_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; 
lean_inc(v_k_1828_);
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1828_, v_v_1829_, v_map_1830_);
if (v_hasTrace_1831_ == 0)
{
lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_1837_ = l_Lean_Name_isPrefixOf(v___x_1836_, v_k_1828_);
lean_dec(v_k_1828_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1835_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*1, v___x_1837_);
return v___x_1839_;
}
}
else
{
lean_object* v___x_1842_; 
lean_dec(v_k_1828_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1842_ = v___x_1833_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*1, v_hasTrace_1831_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1845_){
_start:
{
lean_object* v_subExpr_1847_; lean_object* v_pos_1848_; lean_object* v___x_1849_; 
v_subExpr_1847_ = lean_ctor_get(v___y_1845_, 3);
v_pos_1848_ = lean_ctor_get(v_subExpr_1847_, 1);
lean_inc(v_pos_1848_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_pos_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1850_);
lean_dec_ref(v___y_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1853_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1869_, lean_object* v_k_1870_){
_start:
{
if (lean_obj_tag(v_t_1869_) == 0)
{
lean_object* v_k_1871_; lean_object* v_v_1872_; lean_object* v_l_1873_; lean_object* v_r_1874_; uint8_t v___x_1875_; 
v_k_1871_ = lean_ctor_get(v_t_1869_, 1);
v_v_1872_ = lean_ctor_get(v_t_1869_, 2);
v_l_1873_ = lean_ctor_get(v_t_1869_, 3);
v_r_1874_ = lean_ctor_get(v_t_1869_, 4);
v___x_1875_ = lean_nat_dec_lt(v_k_1870_, v_k_1871_);
if (v___x_1875_ == 0)
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_nat_dec_eq(v_k_1870_, v_k_1871_);
if (v___x_1876_ == 0)
{
v_t_1869_ = v_r_1874_;
goto _start;
}
else
{
lean_object* v___x_1878_; 
lean_inc(v_v_1872_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_v_1872_);
return v___x_1878_;
}
}
else
{
v_t_1869_ = v_l_1873_;
goto _start;
}
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_box(0);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1881_, lean_object* v_k_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1881_, v_k_1882_);
lean_dec(v_k_1882_);
lean_dec(v_t_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_k_1887_; lean_object* v_v_1888_; lean_object* v_l_1889_; lean_object* v_r_1890_; lean_object* v___x_1891_; lean_object* v_a_1892_; lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_k_1887_ = lean_ctor_get(v_x_1885_, 1);
lean_inc(v_k_1887_);
v_v_1888_ = lean_ctor_get(v_x_1885_, 2);
lean_inc(v_v_1888_);
v_l_1889_ = lean_ctor_get(v_x_1885_, 3);
lean_inc(v_l_1889_);
v_r_1890_ = lean_ctor_get(v_x_1885_, 4);
lean_inc(v_r_1890_);
lean_dec_ref_known(v_x_1885_, 5);
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1884_, v_l_1889_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v_a_1893_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_a_1893_);
lean_dec(v_a_1892_);
v___x_1894_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1893_, v_k_1887_, v_v_1888_);
v_init_1884_ = v___x_1894_;
v_x_1885_ = v_r_1890_;
goto _start;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_init_1884_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1898_, v_x_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1932_; 
v___x_1909_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1906_);
v___x_1910_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1902_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_optionsPerPos_1915_; lean_object* v___x_1916_; 
v_optionsPerPos_1915_ = lean_ctor_get(v_a_1902_, 0);
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1915_, v_a_1911_);
lean_dec(v_a_1911_);
if (lean_obj_tag(v___x_1916_) == 1)
{
lean_object* v_val_1917_; lean_object* v_map_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
lean_del_object(v___x_1913_);
v_val_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v_map_1918_ = lean_ctor_get(v_val_1917_, 0);
lean_inc(v_map_1918_);
lean_dec(v_val_1917_);
v___x_1919_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v___x_1909_, v_map_1918_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_a_1924_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_a_1924_);
lean_dec(v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_a_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v___x_1916_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1909_);
v___x_1930_ = v___x_1913_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1909_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1941_, lean_object* v_t_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1942_, v_k_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1945_, lean_object* v_t_1946_, lean_object* v_k_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1945_, v_t_1946_, v_k_1947_);
lean_dec(v_k_1947_);
lean_dec(v_t_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1949_, v_x_1950_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1959_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1986_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_apply_1(v_opt_1969_, v_a_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_opt_1969_);
v_a_1987_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1977_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1977_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_2004_, lean_object* v_opt_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_2014_, lean_object* v_opt_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_2014_, v_opt_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_2024_, lean_object* v_d_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2024_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec_ref(v_d_2025_);
v___x_2036_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; 
lean_inc(v_a_2031_);
lean_inc_ref(v_a_2030_);
lean_inc(v_a_2029_);
lean_inc_ref(v_a_2028_);
lean_inc(v_a_2027_);
lean_inc_ref(v_a_2026_);
v___x_2037_ = lean_apply_7(v_d_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, lean_box(0));
return v___x_2037_;
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_d_2025_);
v_a_2038_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2033_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2033_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2046_, lean_object* v_d_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2046_, v_d_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2056_, lean_object* v_d_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2056_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; uint8_t v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_unbox(v_a_2066_);
lean_dec(v_a_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
lean_inc(v_a_2063_);
lean_inc_ref(v_a_2062_);
lean_inc(v_a_2061_);
lean_inc_ref(v_a_2060_);
lean_inc(v_a_2059_);
lean_inc_ref(v_a_2058_);
v___x_2068_ = lean_apply_7(v_d_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, lean_box(0));
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; 
lean_dec_ref(v_d_2057_);
v___x_2069_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2069_;
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_d_2057_);
v_a_2070_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2065_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2065_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2078_, lean_object* v_d_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2078_, v_d_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2088_, lean_object* v_v_2089_, lean_object* v_t_2090_){
_start:
{
if (lean_obj_tag(v_t_2090_) == 0)
{
lean_object* v_size_2091_; lean_object* v_k_2092_; lean_object* v_v_2093_; lean_object* v_l_2094_; lean_object* v_r_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2376_; 
v_size_2091_ = lean_ctor_get(v_t_2090_, 0);
v_k_2092_ = lean_ctor_get(v_t_2090_, 1);
v_v_2093_ = lean_ctor_get(v_t_2090_, 2);
v_l_2094_ = lean_ctor_get(v_t_2090_, 3);
v_r_2095_ = lean_ctor_get(v_t_2090_, 4);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_t_2090_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2097_ = v_t_2090_;
v_isShared_2098_ = v_isSharedCheck_2376_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_r_2095_);
lean_inc(v_l_2094_);
lean_inc(v_v_2093_);
lean_inc(v_k_2092_);
lean_inc(v_size_2091_);
lean_dec(v_t_2090_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2376_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_nat_dec_lt(v_k_2088_, v_k_2092_);
if (v___x_2099_ == 0)
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_nat_dec_eq(v_k_2088_, v_k_2092_);
if (v___x_2100_ == 0)
{
lean_object* v_impl_2101_; lean_object* v___x_2102_; 
lean_dec(v_size_2091_);
v_impl_2101_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2088_, v_v_2089_, v_r_2095_);
v___x_2102_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2094_) == 0)
{
lean_object* v_size_2103_; lean_object* v_size_2104_; lean_object* v_k_2105_; lean_object* v_v_2106_; lean_object* v_l_2107_; lean_object* v_r_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_size_2103_ = lean_ctor_get(v_l_2094_, 0);
v_size_2104_ = lean_ctor_get(v_impl_2101_, 0);
v_k_2105_ = lean_ctor_get(v_impl_2101_, 1);
v_v_2106_ = lean_ctor_get(v_impl_2101_, 2);
v_l_2107_ = lean_ctor_get(v_impl_2101_, 3);
lean_inc(v_l_2107_);
v_r_2108_ = lean_ctor_get(v_impl_2101_, 4);
v___x_2109_ = lean_unsigned_to_nat(3u);
v___x_2110_ = lean_nat_mul(v___x_2109_, v_size_2103_);
v___x_2111_ = lean_nat_dec_lt(v___x_2110_, v_size_2104_);
lean_dec(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_dec(v_l_2107_);
v___x_2112_ = lean_nat_add(v___x_2102_, v_size_2103_);
v___x_2113_ = lean_nat_add(v___x_2112_, v_size_2104_);
lean_dec(v___x_2112_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_impl_2101_);
lean_ctor_set(v___x_2097_, 0, v___x_2113_);
v___x_2115_ = v___x_2097_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_impl_2101_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
else
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2180_; 
lean_inc(v_r_2108_);
lean_inc(v_v_2106_);
lean_inc(v_k_2105_);
lean_inc(v_size_2104_);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_impl_2101_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2181_ = lean_ctor_get(v_impl_2101_, 4);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_impl_2101_, 3);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_impl_2101_, 2);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_impl_2101_, 1);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_impl_2101_, 0);
lean_dec(v_unused_2185_);
v___x_2118_ = v_impl_2101_;
v_isShared_2119_ = v_isSharedCheck_2180_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v_impl_2101_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2180_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_size_2120_; lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_l_2123_; lean_object* v_r_2124_; lean_object* v_size_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v_size_2120_ = lean_ctor_get(v_l_2107_, 0);
v_k_2121_ = lean_ctor_get(v_l_2107_, 1);
v_v_2122_ = lean_ctor_get(v_l_2107_, 2);
v_l_2123_ = lean_ctor_get(v_l_2107_, 3);
v_r_2124_ = lean_ctor_get(v_l_2107_, 4);
v_size_2125_ = lean_ctor_get(v_r_2108_, 0);
v___x_2126_ = lean_unsigned_to_nat(2u);
v___x_2127_ = lean_nat_mul(v___x_2126_, v_size_2125_);
v___x_2128_ = lean_nat_dec_lt(v_size_2120_, v___x_2127_);
lean_dec(v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2156_; 
lean_inc(v_r_2124_);
lean_inc(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_l_2107_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2157_ = lean_ctor_get(v_l_2107_, 4);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_l_2107_, 3);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_l_2107_, 2);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_l_2107_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_l_2107_, 0);
lean_dec(v_unused_2161_);
v___x_2130_ = v_l_2107_;
v_isShared_2131_ = v_isSharedCheck_2156_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v_l_2107_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2156_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2146_; 
v___x_2132_ = lean_nat_add(v___x_2102_, v_size_2103_);
v___x_2133_ = lean_nat_add(v___x_2132_, v_size_2104_);
lean_dec(v_size_2104_);
if (lean_obj_tag(v_l_2123_) == 0)
{
lean_object* v_size_2154_; 
v_size_2154_ = lean_ctor_get(v_l_2123_, 0);
lean_inc(v_size_2154_);
v___y_2146_ = v_size_2154_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___y_2146_ = v___x_2155_;
goto v___jp_2145_;
}
v___jp_2134_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = lean_nat_add(v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec(v___y_2136_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 4, v_r_2108_);
lean_ctor_set(v___x_2130_, 3, v_r_2124_);
lean_ctor_set(v___x_2130_, 2, v_v_2106_);
lean_ctor_set(v___x_2130_, 1, v_k_2105_);
lean_ctor_set(v___x_2130_, 0, v___x_2138_);
v___x_2140_ = v___x_2130_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2105_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2106_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_r_2108_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 4, v___x_2140_);
lean_ctor_set(v___x_2118_, 3, v___y_2135_);
lean_ctor_set(v___x_2118_, 2, v_v_2122_);
lean_ctor_set(v___x_2118_, 1, v_k_2121_);
lean_ctor_set(v___x_2118_, 0, v___x_2133_);
v___x_2142_ = v___x_2118_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v___y_2135_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
v___jp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_nat_add(v___x_2132_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec(v___x_2132_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_l_2123_);
lean_ctor_set(v___x_2097_, 0, v___x_2147_);
v___x_2149_ = v___x_2097_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_l_2123_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_nat_add(v___x_2102_, v_size_2125_);
if (lean_obj_tag(v_r_2124_) == 0)
{
lean_object* v_size_2151_; 
v_size_2151_ = lean_ctor_get(v_r_2124_, 0);
lean_inc(v_size_2151_);
v___y_2135_ = v___x_2149_;
v___y_2136_ = v___x_2150_;
v___y_2137_ = v_size_2151_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_unsigned_to_nat(0u);
v___y_2135_ = v___x_2149_;
v___y_2136_ = v___x_2150_;
v___y_2137_ = v___x_2152_;
goto v___jp_2134_;
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_del_object(v___x_2097_);
v___x_2162_ = lean_nat_add(v___x_2102_, v_size_2103_);
v___x_2163_ = lean_nat_add(v___x_2162_, v_size_2104_);
lean_dec(v_size_2104_);
v___x_2164_ = lean_nat_add(v___x_2162_, v_size_2120_);
lean_dec(v___x_2162_);
lean_inc_ref(v_l_2094_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 4, v_l_2107_);
lean_ctor_set(v___x_2118_, 3, v_l_2094_);
lean_ctor_set(v___x_2118_, 2, v_v_2093_);
lean_ctor_set(v___x_2118_, 1, v_k_2092_);
lean_ctor_set(v___x_2118_, 0, v___x_2164_);
v___x_2166_ = v___x_2118_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_l_2107_);
v___x_2166_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
v_isSharedCheck_2173_ = !lean_is_exclusive(v_l_2094_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; 
v_unused_2174_ = lean_ctor_get(v_l_2094_, 4);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_l_2094_, 3);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_l_2094_, 2);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_l_2094_, 1);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_l_2094_, 0);
lean_dec(v_unused_2178_);
v___x_2168_ = v_l_2094_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_dec(v_l_2094_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 4, v_r_2108_);
lean_ctor_set(v___x_2168_, 3, v___x_2166_);
lean_ctor_set(v___x_2168_, 2, v_v_2106_);
lean_ctor_set(v___x_2168_, 1, v_k_2105_);
lean_ctor_set(v___x_2168_, 0, v___x_2163_);
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2105_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2106_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_r_2108_);
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
}
}
else
{
lean_object* v_l_2186_; 
v_l_2186_ = lean_ctor_get(v_impl_2101_, 3);
lean_inc(v_l_2186_);
if (lean_obj_tag(v_l_2186_) == 0)
{
lean_object* v_r_2187_; lean_object* v_k_2188_; lean_object* v_v_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2212_; 
v_r_2187_ = lean_ctor_get(v_impl_2101_, 4);
v_k_2188_ = lean_ctor_get(v_impl_2101_, 1);
v_v_2189_ = lean_ctor_get(v_impl_2101_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_impl_2101_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2213_ = lean_ctor_get(v_impl_2101_, 3);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_impl_2101_, 0);
lean_dec(v_unused_2214_);
v___x_2191_ = v_impl_2101_;
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_r_2187_);
lean_inc(v_v_2189_);
lean_inc(v_k_2188_);
lean_dec(v_impl_2101_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2208_; 
v_k_2193_ = lean_ctor_get(v_l_2186_, 1);
v_v_2194_ = lean_ctor_get(v_l_2186_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_l_2186_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2209_ = lean_ctor_get(v_l_2186_, 4);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_l_2186_, 3);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_l_2186_, 0);
lean_dec(v_unused_2211_);
v___x_2196_ = v_l_2186_;
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_l_2186_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2187_, 2);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_r_2187_);
lean_ctor_set(v___x_2196_, 3, v_r_2187_);
lean_ctor_set(v___x_2196_, 2, v_v_2093_);
lean_ctor_set(v___x_2196_, 1, v_k_2092_);
lean_ctor_set(v___x_2196_, 0, v___x_2102_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_r_2187_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_r_2187_);
v___x_2200_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
lean_inc(v_r_2187_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 3, v_r_2187_);
lean_ctor_set(v___x_2191_, 0, v___x_2102_);
v___x_2202_ = v___x_2191_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2188_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2189_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_r_2187_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_r_2187_);
v___x_2202_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2204_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v___x_2202_);
lean_ctor_set(v___x_2097_, 3, v___x_2200_);
lean_ctor_set(v___x_2097_, 2, v_v_2194_);
lean_ctor_set(v___x_2097_, 1, v_k_2193_);
lean_ctor_set(v___x_2097_, 0, v___x_2198_);
v___x_2204_ = v___x_2097_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2194_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
else
{
lean_object* v_r_2215_; 
v_r_2215_ = lean_ctor_get(v_impl_2101_, 4);
lean_inc(v_r_2215_);
if (lean_obj_tag(v_r_2215_) == 0)
{
lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2228_; 
v_k_2216_ = lean_ctor_get(v_impl_2101_, 1);
v_v_2217_ = lean_ctor_get(v_impl_2101_, 2);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_impl_2101_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; 
v_unused_2229_ = lean_ctor_get(v_impl_2101_, 4);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_impl_2101_, 3);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_impl_2101_, 0);
lean_dec(v_unused_2231_);
v___x_2219_ = v_impl_2101_;
v_isShared_2220_ = v_isSharedCheck_2228_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_v_2217_);
lean_inc(v_k_2216_);
lean_dec(v_impl_2101_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2228_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(3u);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 4, v_l_2186_);
lean_ctor_set(v___x_2219_, 2, v_v_2093_);
lean_ctor_set(v___x_2219_, 1, v_k_2092_);
lean_ctor_set(v___x_2219_, 0, v___x_2102_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_l_2186_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_l_2186_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_r_2215_);
lean_ctor_set(v___x_2097_, 3, v___x_2223_);
lean_ctor_set(v___x_2097_, 2, v_v_2217_);
lean_ctor_set(v___x_2097_, 1, v_k_2216_);
lean_ctor_set(v___x_2097_, 0, v___x_2221_);
v___x_2225_ = v___x_2097_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_r_2215_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_unsigned_to_nat(2u);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_impl_2101_);
lean_ctor_set(v___x_2097_, 3, v_r_2215_);
lean_ctor_set(v___x_2097_, 0, v___x_2232_);
v___x_2234_ = v___x_2097_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_r_2215_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_impl_2101_);
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
lean_object* v___x_2237_; 
lean_dec(v_v_2093_);
lean_dec(v_k_2092_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 2, v_v_2089_);
lean_ctor_set(v___x_2097_, 1, v_k_2088_);
v___x_2237_ = v___x_2097_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_size_2091_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_r_2095_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
else
{
lean_object* v_impl_2239_; lean_object* v___x_2240_; 
lean_dec(v_size_2091_);
v_impl_2239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2088_, v_v_2089_, v_l_2094_);
v___x_2240_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2095_) == 0)
{
lean_object* v_size_2241_; lean_object* v_size_2242_; lean_object* v_k_2243_; lean_object* v_v_2244_; lean_object* v_l_2245_; lean_object* v_r_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v_size_2241_ = lean_ctor_get(v_r_2095_, 0);
v_size_2242_ = lean_ctor_get(v_impl_2239_, 0);
v_k_2243_ = lean_ctor_get(v_impl_2239_, 1);
v_v_2244_ = lean_ctor_get(v_impl_2239_, 2);
v_l_2245_ = lean_ctor_get(v_impl_2239_, 3);
v_r_2246_ = lean_ctor_get(v_impl_2239_, 4);
lean_inc(v_r_2246_);
v___x_2247_ = lean_unsigned_to_nat(3u);
v___x_2248_ = lean_nat_mul(v___x_2247_, v_size_2241_);
v___x_2249_ = lean_nat_dec_lt(v___x_2248_, v_size_2242_);
lean_dec(v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec(v_r_2246_);
v___x_2250_ = lean_nat_add(v___x_2240_, v_size_2242_);
v___x_2251_ = lean_nat_add(v___x_2250_, v_size_2241_);
lean_dec(v___x_2250_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 3, v_impl_2239_);
lean_ctor_set(v___x_2097_, 0, v___x_2251_);
v___x_2253_ = v___x_2097_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_impl_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2095_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2320_; 
lean_inc(v_l_2245_);
lean_inc(v_v_2244_);
lean_inc(v_k_2243_);
lean_inc(v_size_2242_);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_impl_2239_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; lean_object* v_unused_2325_; 
v_unused_2321_ = lean_ctor_get(v_impl_2239_, 4);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_impl_2239_, 3);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_impl_2239_, 2);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_impl_2239_, 1);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_impl_2239_, 0);
lean_dec(v_unused_2325_);
v___x_2256_ = v_impl_2239_;
v_isShared_2257_ = v_isSharedCheck_2320_;
goto v_resetjp_2255_;
}
else
{
lean_dec(v_impl_2239_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2320_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_size_2258_; lean_object* v_size_2259_; lean_object* v_k_2260_; lean_object* v_v_2261_; lean_object* v_l_2262_; lean_object* v_r_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_size_2258_ = lean_ctor_get(v_l_2245_, 0);
v_size_2259_ = lean_ctor_get(v_r_2246_, 0);
v_k_2260_ = lean_ctor_get(v_r_2246_, 1);
v_v_2261_ = lean_ctor_get(v_r_2246_, 2);
v_l_2262_ = lean_ctor_get(v_r_2246_, 3);
v_r_2263_ = lean_ctor_get(v_r_2246_, 4);
v___x_2264_ = lean_unsigned_to_nat(2u);
v___x_2265_ = lean_nat_mul(v___x_2264_, v_size_2258_);
v___x_2266_ = lean_nat_dec_lt(v_size_2259_, v___x_2265_);
lean_dec(v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2295_; 
lean_inc(v_r_2263_);
lean_inc(v_l_2262_);
lean_inc(v_v_2261_);
lean_inc(v_k_2260_);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_r_2246_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; 
v_unused_2296_ = lean_ctor_get(v_r_2246_, 4);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_r_2246_, 3);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_r_2246_, 2);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_r_2246_, 1);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_r_2246_, 0);
lean_dec(v_unused_2300_);
v___x_2268_ = v_r_2246_;
v_isShared_2269_ = v_isSharedCheck_2295_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_r_2246_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2295_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___x_2283_; lean_object* v___y_2285_; 
v___x_2270_ = lean_nat_add(v___x_2240_, v_size_2242_);
lean_dec(v_size_2242_);
v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2241_);
lean_dec(v___x_2270_);
v___x_2283_ = lean_nat_add(v___x_2240_, v_size_2258_);
if (lean_obj_tag(v_l_2262_) == 0)
{
lean_object* v_size_2293_; 
v_size_2293_ = lean_ctor_get(v_l_2262_, 0);
lean_inc(v_size_2293_);
v___y_2285_ = v_size_2293_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_unsigned_to_nat(0u);
v___y_2285_ = v___x_2294_;
goto v___jp_2284_;
}
v___jp_2272_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_nat_add(v___y_2273_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec(v___y_2273_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_r_2095_);
lean_ctor_set(v___x_2268_, 3, v_r_2263_);
lean_ctor_set(v___x_2268_, 2, v_v_2093_);
lean_ctor_set(v___x_2268_, 1, v_k_2092_);
lean_ctor_set(v___x_2268_, 0, v___x_2276_);
v___x_2278_ = v___x_2268_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_r_2263_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_r_2095_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v___x_2278_);
lean_ctor_set(v___x_2256_, 3, v___y_2274_);
lean_ctor_set(v___x_2256_, 2, v_v_2261_);
lean_ctor_set(v___x_2256_, 1, v_k_2260_);
lean_ctor_set(v___x_2256_, 0, v___x_2271_);
v___x_2280_ = v___x_2256_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v___y_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
v___jp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_nat_add(v___x_2283_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec(v___x_2283_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_l_2262_);
lean_ctor_set(v___x_2097_, 3, v_l_2245_);
lean_ctor_set(v___x_2097_, 2, v_v_2244_);
lean_ctor_set(v___x_2097_, 1, v_k_2243_);
lean_ctor_set(v___x_2097_, 0, v___x_2286_);
v___x_2288_ = v___x_2097_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2243_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2244_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_l_2245_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_l_2262_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_nat_add(v___x_2240_, v_size_2241_);
if (lean_obj_tag(v_r_2263_) == 0)
{
lean_object* v_size_2290_; 
v_size_2290_ = lean_ctor_get(v_r_2263_, 0);
lean_inc(v_size_2290_);
v___y_2273_ = v___x_2289_;
v___y_2274_ = v___x_2288_;
v___y_2275_ = v_size_2290_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___y_2273_ = v___x_2289_;
v___y_2274_ = v___x_2288_;
v___y_2275_ = v___x_2291_;
goto v___jp_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_del_object(v___x_2097_);
v___x_2301_ = lean_nat_add(v___x_2240_, v_size_2242_);
lean_dec(v_size_2242_);
v___x_2302_ = lean_nat_add(v___x_2301_, v_size_2241_);
lean_dec(v___x_2301_);
v___x_2303_ = lean_nat_add(v___x_2240_, v_size_2241_);
v___x_2304_ = lean_nat_add(v___x_2303_, v_size_2259_);
lean_dec(v___x_2303_);
lean_inc_ref(v_r_2095_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v_r_2095_);
lean_ctor_set(v___x_2256_, 3, v_r_2246_);
lean_ctor_set(v___x_2256_, 2, v_v_2093_);
lean_ctor_set(v___x_2256_, 1, v_k_2092_);
lean_ctor_set(v___x_2256_, 0, v___x_2304_);
v___x_2306_ = v___x_2256_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_r_2246_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_2095_);
v___x_2306_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_isSharedCheck_2313_ = !lean_is_exclusive(v_r_2095_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; lean_object* v_unused_2318_; 
v_unused_2314_ = lean_ctor_get(v_r_2095_, 4);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_r_2095_, 3);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_r_2095_, 2);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_r_2095_, 1);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_r_2095_, 0);
lean_dec(v_unused_2318_);
v___x_2308_ = v_r_2095_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v_r_2095_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v___x_2306_);
lean_ctor_set(v___x_2308_, 3, v_l_2245_);
lean_ctor_set(v___x_2308_, 2, v_v_2244_);
lean_ctor_set(v___x_2308_, 1, v_k_2243_);
lean_ctor_set(v___x_2308_, 0, v___x_2302_);
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2243_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2244_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_l_2245_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v___x_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2326_; 
v_l_2326_ = lean_ctor_get(v_impl_2239_, 3);
if (lean_obj_tag(v_l_2326_) == 0)
{
lean_object* v_r_2327_; lean_object* v_k_2328_; lean_object* v_v_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
lean_inc_ref(v_l_2326_);
v_r_2327_ = lean_ctor_get(v_impl_2239_, 4);
v_k_2328_ = lean_ctor_get(v_impl_2239_, 1);
v_v_2329_ = lean_ctor_get(v_impl_2239_, 2);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_impl_2239_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; lean_object* v_unused_2342_; 
v_unused_2341_ = lean_ctor_get(v_impl_2239_, 3);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_impl_2239_, 0);
lean_dec(v_unused_2342_);
v___x_2331_ = v_impl_2239_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_r_2327_);
lean_inc(v_v_2329_);
lean_inc(v_k_2328_);
lean_dec(v_impl_2239_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2327_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 3, v_r_2327_);
lean_ctor_set(v___x_2331_, 2, v_v_2093_);
lean_ctor_set(v___x_2331_, 1, v_k_2092_);
lean_ctor_set(v___x_2331_, 0, v___x_2240_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_r_2327_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v_r_2327_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v___x_2335_);
lean_ctor_set(v___x_2097_, 3, v_l_2326_);
lean_ctor_set(v___x_2097_, 2, v_v_2329_);
lean_ctor_set(v___x_2097_, 1, v_k_2328_);
lean_ctor_set(v___x_2097_, 0, v___x_2333_);
v___x_2337_ = v___x_2097_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_k_2328_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_v_2329_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_l_2326_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_r_2343_; 
v_r_2343_ = lean_ctor_get(v_impl_2239_, 4);
lean_inc(v_r_2343_);
if (lean_obj_tag(v_r_2343_) == 0)
{
lean_object* v_k_2344_; lean_object* v_v_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2368_; 
lean_inc(v_l_2326_);
v_k_2344_ = lean_ctor_get(v_impl_2239_, 1);
v_v_2345_ = lean_ctor_get(v_impl_2239_, 2);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_impl_2239_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; 
v_unused_2369_ = lean_ctor_get(v_impl_2239_, 4);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_impl_2239_, 3);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_impl_2239_, 0);
lean_dec(v_unused_2371_);
v___x_2347_ = v_impl_2239_;
v_isShared_2348_ = v_isSharedCheck_2368_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_v_2345_);
lean_inc(v_k_2344_);
lean_dec(v_impl_2239_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2368_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v_k_2349_; lean_object* v_v_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2364_; 
v_k_2349_ = lean_ctor_get(v_r_2343_, 1);
v_v_2350_ = lean_ctor_get(v_r_2343_, 2);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_r_2343_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; 
v_unused_2365_ = lean_ctor_get(v_r_2343_, 4);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_2343_, 3);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_r_2343_, 0);
lean_dec(v_unused_2367_);
v___x_2352_ = v_r_2343_;
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_v_2350_);
lean_inc(v_k_2349_);
lean_dec(v_r_2343_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_unsigned_to_nat(3u);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 4, v_l_2326_);
lean_ctor_set(v___x_2352_, 3, v_l_2326_);
lean_ctor_set(v___x_2352_, 2, v_v_2345_);
lean_ctor_set(v___x_2352_, 1, v_k_2344_);
lean_ctor_set(v___x_2352_, 0, v___x_2240_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_k_2344_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_v_2345_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v_l_2326_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v_l_2326_);
v___x_2356_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 4, v_l_2326_);
lean_ctor_set(v___x_2347_, 2, v_v_2093_);
lean_ctor_set(v___x_2347_, 1, v_k_2092_);
lean_ctor_set(v___x_2347_, 0, v___x_2240_);
v___x_2358_ = v___x_2347_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_l_2326_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_l_2326_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v___x_2358_);
lean_ctor_set(v___x_2097_, 3, v___x_2356_);
lean_ctor_set(v___x_2097_, 2, v_v_2350_);
lean_ctor_set(v___x_2097_, 1, v_k_2349_);
lean_ctor_set(v___x_2097_, 0, v___x_2354_);
v___x_2360_ = v___x_2097_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_k_2349_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_v_2350_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2361_, 4, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_unsigned_to_nat(2u);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_r_2343_);
lean_ctor_set(v___x_2097_, 3, v_impl_2239_);
lean_ctor_set(v___x_2097_, 0, v___x_2372_);
v___x_2374_ = v___x_2097_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_impl_2239_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_r_2343_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v_k_2088_);
lean_ctor_set(v___x_2378_, 2, v_v_2089_);
lean_ctor_set(v___x_2378_, 3, v_t_2090_);
lean_ctor_set(v___x_2378_, 4, v_t_2090_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2379_, lean_object* v_v_2380_, lean_object* v_x_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v_a_2390_; lean_object* v_optionsPerPos_2391_; lean_object* v_currNamespace_2392_; lean_object* v_openDecls_2393_; uint8_t v_inPattern_2394_; lean_object* v_subExpr_2395_; lean_object* v_depth_2396_; lean_object* v_lctxInitIndices_2397_; lean_object* v___y_2399_; lean_object* v___x_2404_; 
v___x_2389_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2382_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v___x_2389_);
v_optionsPerPos_2391_ = lean_ctor_get(v_a_2382_, 0);
v_currNamespace_2392_ = lean_ctor_get(v_a_2382_, 1);
v_openDecls_2393_ = lean_ctor_get(v_a_2382_, 2);
v_inPattern_2394_ = lean_ctor_get_uint8(v_a_2382_, sizeof(void*)*6);
v_subExpr_2395_ = lean_ctor_get(v_a_2382_, 3);
v_depth_2396_ = lean_ctor_get(v_a_2382_, 4);
v_lctxInitIndices_2397_ = lean_ctor_get(v_a_2382_, 5);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2391_, v_a_2390_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Options_empty;
v___y_2399_ = v___x_2405_;
goto v___jp_2398_;
}
else
{
lean_object* v_val_2406_; 
v_val_2406_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v___x_2404_, 1);
v___y_2399_ = v_val_2406_;
goto v___jp_2398_;
}
v___jp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2399_, v_k_2379_, v_v_2380_);
lean_inc(v_optionsPerPos_2391_);
v___x_2401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2390_, v___x_2400_, v_optionsPerPos_2391_);
lean_inc(v_lctxInitIndices_2397_);
lean_inc(v_depth_2396_);
lean_inc_ref(v_subExpr_2395_);
lean_inc(v_openDecls_2393_);
lean_inc(v_currNamespace_2392_);
v___x_2402_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v_currNamespace_2392_);
lean_ctor_set(v___x_2402_, 2, v_openDecls_2393_);
lean_ctor_set(v___x_2402_, 3, v_subExpr_2395_);
lean_ctor_set(v___x_2402_, 4, v_depth_2396_);
lean_ctor_set(v___x_2402_, 5, v_lctxInitIndices_2397_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*6, v_inPattern_2394_);
lean_inc(v_a_2387_);
lean_inc_ref(v_a_2386_);
lean_inc(v_a_2385_);
lean_inc_ref(v_a_2384_);
lean_inc(v_a_2383_);
v___x_2403_ = lean_apply_7(v_x_2381_, v___x_2402_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, lean_box(0));
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2407_, lean_object* v_v_2408_, lean_object* v_x_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2407_, v_v_2408_, v_x_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2418_, lean_object* v_k_2419_, lean_object* v_v_2420_, lean_object* v_x_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2419_, v_v_2420_, v_x_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2430_, lean_object* v_k_2431_, lean_object* v_v_2432_, lean_object* v_x_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2430_, v_k_2431_, v_v_2432_, v_x_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2442_, lean_object* v_k_2443_, lean_object* v_v_2444_, lean_object* v_t_2445_, lean_object* v_hl_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2443_, v_v_2444_, v_t_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2448_, lean_object* v_stx_2449_){
_start:
{
uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = 0;
lean_inc(v_pos_2448_);
v___x_2451_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2451_, 0, v_pos_2448_);
lean_ctor_set(v___x_2451_, 1, v_pos_2448_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*2, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_setInfo(v___x_2451_, v_stx_2449_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v___x_2456_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2454_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2461_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2457_, v_stx_2453_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2466_, v_a_2467_);
lean_dec_ref(v_a_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2470_, v_a_2471_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2490_, lean_object* v_e_2491_, uint8_t v_isBinder_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_lctx_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_lctx_2495_ = lean_ctor_get(v_a_2493_, 2);
v___x_2496_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v_stx_2490_);
v___x_2498_ = lean_box(0);
v___x_2499_ = 0;
lean_inc_ref(v_lctx_2495_);
v___x_2500_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2500_, 0, v___x_2497_);
lean_ctor_set(v___x_2500_, 1, v_lctx_2495_);
lean_ctor_set(v___x_2500_, 2, v___x_2498_);
lean_ctor_set(v___x_2500_, 3, v_e_2491_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*4, v_isBinder_2492_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*4 + 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2502_, lean_object* v_e_2503_, lean_object* v_isBinder_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
uint8_t v_isBinder_boxed_2507_; lean_object* v_res_2508_; 
v_isBinder_boxed_2507_ = lean_unbox(v_isBinder_2504_);
v_res_2508_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2502_, v_e_2503_, v_isBinder_boxed_2507_, v_a_2505_);
lean_dec_ref(v_a_2505_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2509_, lean_object* v_e_2510_, uint8_t v_isBinder_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2509_, v_e_2510_, v_isBinder_2511_, v_a_2514_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2520_, lean_object* v_e_2521_, lean_object* v_isBinder_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
uint8_t v_isBinder_boxed_2530_; lean_object* v_res_2531_; 
v_isBinder_boxed_2530_ = lean_unbox(v_isBinder_2522_);
v_res_2531_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2520_, v_e_2521_, v_isBinder_boxed_2530_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2532_, lean_object* v_stx_2533_, lean_object* v_e_2534_, uint8_t v_isBinder_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2562_; 
v___x_2539_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2533_, v_e_2534_, v_isBinder_2535_, v_a_2537_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_steps_2546_; lean_object* v_infos_2547_; lean_object* v_holeIter_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2561_; 
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_a_2540_);
v___x_2545_ = lean_st_ref_take(v_a_2536_);
v_steps_2546_ = lean_ctor_get(v___x_2545_, 0);
v_infos_2547_ = lean_ctor_get(v___x_2545_, 1);
v_holeIter_2548_ = lean_ctor_get(v___x_2545_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2550_ = v___x_2545_;
v_isShared_2551_ = v_isSharedCheck_2561_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_holeIter_2548_);
lean_inc(v_infos_2547_);
lean_inc(v_steps_2546_);
lean_dec(v___x_2545_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2561_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_box(0);
v___x_2553_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2532_, v___x_2544_, v_infos_2547_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_steps_2546_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_holeIter_2548_);
v___x_2555_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_st_ref_put(v_a_2536_, v___x_2555_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2552_);
v___x_2558_ = v___x_2542_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2552_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2563_, lean_object* v_stx_2564_, lean_object* v_e_2565_, lean_object* v_isBinder_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
uint8_t v_isBinder_boxed_2570_; lean_object* v_res_2571_; 
v_isBinder_boxed_2570_ = lean_unbox(v_isBinder_2566_);
v_res_2571_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2563_, v_stx_2564_, v_e_2565_, v_isBinder_boxed_2570_, v_a_2567_, v_a_2568_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2572_, lean_object* v_stx_2573_, lean_object* v_e_2574_, uint8_t v_isBinder_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2572_, v_stx_2573_, v_e_2574_, v_isBinder_2575_, v_a_2577_, v_a_2578_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2584_, lean_object* v_stx_2585_, lean_object* v_e_2586_, lean_object* v_isBinder_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
uint8_t v_isBinder_boxed_2595_; lean_object* v_res_2596_; 
v_isBinder_boxed_2595_ = lean_unbox(v_isBinder_2587_);
v_res_2596_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2584_, v_stx_2585_, v_e_2586_, v_isBinder_boxed_2595_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2597_, lean_object* v_fieldName_2598_, lean_object* v_stx_2599_, lean_object* v_val_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_lctx_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_lctx_2603_ = lean_ctor_get(v_a_2601_, 2);
lean_inc_ref(v_lctx_2603_);
v___x_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2604_, 0, v_projName_2597_);
lean_ctor_set(v___x_2604_, 1, v_fieldName_2598_);
lean_ctor_set(v___x_2604_, 2, v_lctx_2603_);
lean_ctor_set(v___x_2604_, 3, v_val_2600_);
lean_ctor_set(v___x_2604_, 4, v_stx_2599_);
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2606_, lean_object* v_fieldName_2607_, lean_object* v_stx_2608_, lean_object* v_val_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2606_, v_fieldName_2607_, v_stx_2608_, v_val_2609_, v_a_2610_);
lean_dec_ref(v_a_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2613_, lean_object* v_fieldName_2614_, lean_object* v_stx_2615_, lean_object* v_val_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2613_, v_fieldName_2614_, v_stx_2615_, v_val_2616_, v_a_2619_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2625_, lean_object* v_fieldName_2626_, lean_object* v_stx_2627_, lean_object* v_val_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2625_, v_fieldName_2626_, v_stx_2627_, v_val_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2637_, lean_object* v_projName_2638_, lean_object* v_fieldName_2639_, lean_object* v_stx_2640_, lean_object* v_val_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2668_; 
v___x_2645_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2638_, v_fieldName_2639_, v_stx_2640_, v_val_2641_, v_a_2643_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_steps_2652_; lean_object* v_infos_2653_; lean_object* v_holeIter_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2667_; 
v___x_2650_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_a_2646_);
v___x_2651_ = lean_st_ref_take(v_a_2642_);
v_steps_2652_ = lean_ctor_get(v___x_2651_, 0);
v_infos_2653_ = lean_ctor_get(v___x_2651_, 1);
v_holeIter_2654_ = lean_ctor_get(v___x_2651_, 2);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2656_ = v___x_2651_;
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_holeIter_2654_);
lean_inc(v_infos_2653_);
lean_inc(v_steps_2652_);
lean_dec(v___x_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2658_ = lean_box(0);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2637_, v___x_2650_, v_infos_2653_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_steps_2652_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_holeIter_2654_);
v___x_2661_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_st_ref_put(v_a_2642_, v___x_2661_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2658_);
v___x_2664_ = v___x_2648_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2658_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2669_, lean_object* v_projName_2670_, lean_object* v_fieldName_2671_, lean_object* v_stx_2672_, lean_object* v_val_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2669_, v_projName_2670_, v_fieldName_2671_, v_stx_2672_, v_val_2673_, v_a_2674_, v_a_2675_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2678_, lean_object* v_projName_2679_, lean_object* v_fieldName_2680_, lean_object* v_stx_2681_, lean_object* v_val_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2678_, v_projName_2679_, v_fieldName_2680_, v_stx_2681_, v_val_2682_, v_a_2684_, v_a_2685_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2691_, lean_object* v_projName_2692_, lean_object* v_fieldName_2693_, lean_object* v_stx_2694_, lean_object* v_val_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2691_, v_projName_2692_, v_fieldName_2693_, v_stx_2694_, v_val_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_val_2704_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2708_, v___y_2709_);
lean_dec_ref(v___y_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2712_, lean_object* v_stx_2713_, lean_object* v_e_2714_, uint8_t v_isBinder_2715_, lean_object* v_location_x3f_2716_, lean_object* v_docString_x3f_2717_, lean_object* v_mkDocString_x3f_2718_, uint8_t v_explicit_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2758_; 
v___x_2723_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2713_, v_e_2714_, v_isBinder_2715_, v_a_2721_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2758_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2758_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___y_2729_; 
if (lean_obj_tag(v_mkDocString_x3f_2718_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2717_) == 0)
{
v___y_2729_ = v_mkDocString_x3f_2718_;
goto v___jp_2728_;
}
else
{
lean_object* v_val_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2757_; 
v_val_2749_ = lean_ctor_get(v_docString_x3f_2717_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_docString_x3f_2717_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2751_ = v_docString_x3f_2717_;
v_isShared_2752_ = v_isSharedCheck_2757_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_val_2749_);
lean_dec(v_docString_x3f_2717_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2757_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___f_2753_; lean_object* v___x_2755_; 
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2753_, 0, v_val_2749_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___f_2753_);
v___x_2755_ = v___x_2751_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___f_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
v___y_2729_ = v___x_2755_;
goto v___jp_2728_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2717_);
v___y_2729_ = v_mkDocString_x3f_2718_;
goto v___jp_2728_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v_steps_2733_; lean_object* v_infos_2734_; lean_object* v_holeIter_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2748_; 
v___x_2730_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2730_, 0, v_a_2724_);
lean_ctor_set(v___x_2730_, 1, v_location_x3f_2716_);
lean_ctor_set(v___x_2730_, 2, v___y_2729_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*3, v_explicit_2719_);
v___x_2731_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
v___x_2732_ = lean_st_ref_take(v_a_2720_);
v_steps_2733_ = lean_ctor_get(v___x_2732_, 0);
v_infos_2734_ = lean_ctor_get(v___x_2732_, 1);
v_holeIter_2735_ = lean_ctor_get(v___x_2732_, 2);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2737_ = v___x_2732_;
v_isShared_2738_ = v_isSharedCheck_2748_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_holeIter_2735_);
lean_inc(v_infos_2734_);
lean_inc(v_steps_2733_);
lean_dec(v___x_2732_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2748_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2739_ = lean_box(0);
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2712_, v___x_2731_, v_infos_2734_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v___x_2740_);
v___x_2742_ = v___x_2737_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_steps_2733_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_holeIter_2735_);
v___x_2742_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2743_ = lean_st_ref_put(v_a_2720_, v___x_2742_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2739_);
v___x_2745_ = v___x_2726_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2739_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2759_, lean_object* v_stx_2760_, lean_object* v_e_2761_, lean_object* v_isBinder_2762_, lean_object* v_location_x3f_2763_, lean_object* v_docString_x3f_2764_, lean_object* v_mkDocString_x3f_2765_, lean_object* v_explicit_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_isBinder_boxed_2770_; uint8_t v_explicit_boxed_2771_; lean_object* v_res_2772_; 
v_isBinder_boxed_2770_ = lean_unbox(v_isBinder_2762_);
v_explicit_boxed_2771_ = lean_unbox(v_explicit_2766_);
v_res_2772_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2759_, v_stx_2760_, v_e_2761_, v_isBinder_boxed_2770_, v_location_x3f_2763_, v_docString_x3f_2764_, v_mkDocString_x3f_2765_, v_explicit_boxed_2771_, v_a_2767_, v_a_2768_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2773_, lean_object* v_stx_2774_, lean_object* v_e_2775_, uint8_t v_isBinder_2776_, lean_object* v_location_x3f_2777_, lean_object* v_docString_x3f_2778_, lean_object* v_mkDocString_x3f_2779_, uint8_t v_explicit_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2773_, v_stx_2774_, v_e_2775_, v_isBinder_2776_, v_location_x3f_2777_, v_docString_x3f_2778_, v_mkDocString_x3f_2779_, v_explicit_2780_, v_a_2782_, v_a_2783_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2789_, lean_object* v_stx_2790_, lean_object* v_e_2791_, lean_object* v_isBinder_2792_, lean_object* v_location_x3f_2793_, lean_object* v_docString_x3f_2794_, lean_object* v_mkDocString_x3f_2795_, lean_object* v_explicit_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
uint8_t v_isBinder_boxed_2804_; uint8_t v_explicit_boxed_2805_; lean_object* v_res_2806_; 
v_isBinder_boxed_2804_ = lean_unbox(v_isBinder_2792_);
v_explicit_boxed_2805_ = lean_unbox(v_explicit_2796_);
v_res_2806_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2789_, v_stx_2790_, v_e_2791_, v_isBinder_boxed_2804_, v_location_x3f_2793_, v_docString_x3f_2794_, v_mkDocString_x3f_2795_, v_explicit_boxed_2805_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v_a_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_n(v_a_2813_, 2);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2808_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2808_);
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = 0;
v___x_2819_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2815_, v_a_2813_, v_a_2817_, v___x_2818_, v_a_2809_, v_a_2810_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2827_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_a_2813_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2813_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2813_);
v_a_2828_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2819_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2819_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2859_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2860_, lean_object* v_t_2861_){
_start:
{
if (lean_obj_tag(v_t_2861_) == 0)
{
lean_object* v_k_2862_; lean_object* v_l_2863_; lean_object* v_r_2864_; uint8_t v___x_2865_; 
v_k_2862_ = lean_ctor_get(v_t_2861_, 1);
v_l_2863_ = lean_ctor_get(v_t_2861_, 3);
v_r_2864_ = lean_ctor_get(v_t_2861_, 4);
v___x_2865_ = lean_nat_dec_lt(v_k_2860_, v_k_2862_);
if (v___x_2865_ == 0)
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_nat_dec_eq(v_k_2860_, v_k_2862_);
if (v___x_2866_ == 0)
{
v_t_2861_ = v_r_2864_;
goto _start;
}
else
{
return v___x_2866_;
}
}
else
{
v_t_2861_ = v_l_2863_;
goto _start;
}
}
else
{
uint8_t v___x_2869_; 
v___x_2869_ = 0;
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2870_, lean_object* v_t_2871_){
_start:
{
uint8_t v_res_2872_; lean_object* v_r_2873_; 
v_res_2872_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2870_, v_t_2871_);
lean_dec(v_t_2871_);
lean_dec(v_k_2870_);
v_r_2873_ = lean_box(v_res_2872_);
return v_r_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Syntax_getInfo_x3f(v_stx_2874_);
if (lean_obj_tag(v___x_2879_) == 1)
{
lean_object* v_val_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2898_; 
v_val_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2898_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_val_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2898_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
if (lean_obj_tag(v_val_2880_) == 1)
{
uint8_t v_canonical_2884_; 
v_canonical_2884_ = lean_ctor_get_uint8(v_val_2880_, sizeof(void*)*2);
if (v_canonical_2884_ == 0)
{
lean_object* v_pos_2885_; lean_object* v_endPos_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_pos_2885_ = lean_ctor_get(v_val_2880_, 0);
lean_inc(v_pos_2885_);
v_endPos_2886_ = lean_ctor_get(v_val_2880_, 1);
lean_inc(v_endPos_2886_);
lean_dec_ref_known(v_val_2880_, 2);
v___x_2887_ = lean_st_ref_get(v_a_2876_);
v___x_2888_ = lean_nat_dec_eq(v_pos_2885_, v_endPos_2886_);
lean_dec(v_endPos_2886_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; 
lean_dec(v___x_2887_);
lean_dec(v_pos_2885_);
lean_del_object(v___x_2882_);
v___x_2889_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2889_;
}
else
{
lean_object* v_infos_2890_; uint8_t v___x_2891_; 
v_infos_2890_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_infos_2890_);
lean_dec(v___x_2887_);
v___x_2891_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2885_, v_infos_2890_);
lean_dec(v_infos_2890_);
lean_dec(v_pos_2885_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_del_object(v___x_2882_);
v___x_2892_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2892_;
}
else
{
lean_object* v___x_2894_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 0);
lean_ctor_set(v___x_2882_, 0, v_stx_2874_);
v___x_2894_ = v___x_2882_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_stx_2874_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v___x_2896_; 
lean_dec_ref_known(v_val_2880_, 2);
lean_del_object(v___x_2882_);
v___x_2896_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2896_;
}
}
else
{
lean_object* v___x_2897_; 
lean_del_object(v___x_2882_);
lean_dec(v_val_2880_);
v___x_2897_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2897_;
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v___x_2879_);
v___x_2899_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2923_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2924_, lean_object* v_k_2925_, lean_object* v_t_2926_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2925_, v_t_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2928_, lean_object* v_k_2929_, lean_object* v_t_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2928_, v_k_2929_, v_t_2930_);
lean_dec(v_t_2930_);
lean_dec(v_k_2929_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v___x_2941_; 
lean_inc(v_a_2939_);
lean_inc_ref(v_a_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_a_2936_);
lean_inc(v_a_2935_);
lean_inc_ref(v_a_2934_);
v___x_2941_ = lean_apply_7(v_d_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, lean_box(0));
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2942_, v_a_2934_, v_a_2935_, v_a_2936_);
return v___x_2943_;
}
else
{
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___x_2961_; 
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
lean_inc(v_a_2955_);
lean_inc_ref(v_a_2954_);
v___x_2961_ = lean_apply_7(v_d_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, lean_box(0));
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2962_, v_a_2954_, v_a_2955_, v_a_2956_);
return v___x_2963_;
}
else
{
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
return v_res_2972_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2973_, lean_object* v_suggestion_x27_2974_, lean_object* v_x_2975_){
_start:
{
if (lean_obj_tag(v_x_2975_) == 1)
{
lean_object* v_fvarId_2976_; lean_object* v___x_2977_; 
v_fvarId_2976_ = lean_ctor_get(v_x_2975_, 0);
lean_inc(v_fvarId_2976_);
lean_dec_ref_known(v_x_2975_, 1);
v___x_2977_ = lean_local_ctx_find(v_lctx_2973_, v_fvarId_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
uint8_t v___x_2978_; 
v___x_2978_ = 0;
return v___x_2978_;
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_val_2979_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2980_ = l_Lean_LocalDecl_userName(v_val_2979_);
lean_dec(v_val_2979_);
v___x_2981_ = lean_name_eq(v___x_2980_, v_suggestion_x27_2974_);
lean_dec(v___x_2980_);
return v___x_2981_;
}
}
else
{
uint8_t v___x_2982_; 
lean_dec_ref(v_x_2975_);
lean_dec_ref(v_lctx_2973_);
v___x_2982_ = 0;
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2983_, lean_object* v_suggestion_x27_2984_, lean_object* v_x_2985_){
_start:
{
uint8_t v_res_2986_; lean_object* v_r_2987_; 
v_res_2986_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2983_, v_suggestion_x27_2984_, v_x_2985_);
lean_dec(v_suggestion_x27_2984_);
v_r_2987_ = lean_box(v_res_2986_);
return v_r_2987_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2988_, lean_object* v_lctx_2989_, lean_object* v_suggestion_x27_2990_){
_start:
{
lean_object* v___f_2991_; lean_object* v___x_2992_; 
v___f_2991_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2991_, 0, v_lctx_2989_);
lean_closure_set(v___f_2991_, 1, v_suggestion_x27_2990_);
v___x_2992_ = lean_find_expr(v___f_2991_, v_body_2988_);
lean_dec_ref(v___f_2991_);
if (lean_obj_tag(v___x_2992_) == 0)
{
uint8_t v___x_2993_; 
v___x_2993_ = 0;
return v___x_2993_;
}
else
{
uint8_t v___x_2994_; 
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = 1;
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2995_, lean_object* v_lctx_2996_, lean_object* v_suggestion_x27_2997_){
_start:
{
uint8_t v_res_2998_; lean_object* v_r_2999_; 
v_res_2998_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2995_, v_lctx_2996_, v_suggestion_x27_2997_);
lean_dec_ref(v_body_2995_);
v_r_2999_ = lean_box(v_res_2998_);
return v_r_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_toCold_3004_; lean_object* v_quotContext_3005_; lean_object* v_currMacroScope_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_toCold_3004_ = lean_ctor_get(v___y_3001_, 0);
lean_inc_ref(v_toCold_3004_);
lean_dec_ref(v___y_3001_);
v_quotContext_3005_ = lean_ctor_get(v_toCold_3004_, 8);
lean_inc(v_quotContext_3005_);
v_currMacroScope_3006_ = lean_ctor_get(v_toCold_3004_, 9);
lean_inc(v_currMacroScope_3006_);
lean_dec_ref(v_toCold_3004_);
v___x_3007_ = l_Lean_addMacroScope(v_quotContext_3005_, v_snd_3000_, v_currMacroScope_3006_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_3018_, lean_object* v_body_3019_, uint8_t v_preserveName_3020_, lean_object* v_avoid_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; uint8_t v_fst_3061_; lean_object* v_snd_3062_; uint8_t v___x_3068_; 
v___x_3068_ = l_Lean_Name_isAnonymous(v_suggestion_3018_);
if (v___x_3068_ == 0)
{
uint8_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = l_Lean_Name_hasMacroScopes(v_suggestion_3018_);
v___x_3070_ = l_Lean_Name_eraseMacroScopes(v_suggestion_3018_);
v_fst_3061_ = v___x_3069_;
v_snd_3062_ = v___x_3070_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3071_; 
v___x_3071_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3061_ = v___x_3068_;
v_snd_3062_ = v___x_3071_;
goto v___jp_3060_;
}
v___jp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = l_Lean_LocalContext_getUnusedName(v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
v___jp_3034_:
{
if (v_preserveName_3020_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec_ref(v___y_3036_);
v___x_3038_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3039_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3038_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3050_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_unbox(v_a_3040_);
lean_dec(v_a_3040_);
if (v___x_3044_ == 0)
{
lean_del_object(v___x_3042_);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3037_;
goto v___jp_3029_;
}
else
{
uint8_t v___x_3045_; 
v___x_3045_ = l_Lean_NameSet_contains(v_avoid_3021_, v___y_3037_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
lean_inc(v___y_3037_);
lean_inc_ref(v___y_3035_);
v___x_3046_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_3019_, v___y_3035_, v___y_3037_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3048_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___y_3037_);
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___y_3037_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
else
{
lean_del_object(v___x_3042_);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3037_;
goto v___jp_3029_;
}
}
else
{
lean_del_object(v___x_3042_);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3037_;
goto v___jp_3029_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v___y_3037_);
v_a_3051_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3039_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3039_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v___x_3059_; 
lean_dec(v___y_3037_);
v___x_3059_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3036_, v_a_3026_, v_a_3027_);
return v___x_3059_;
}
}
v___jp_3060_:
{
lean_object* v_lctx_3063_; uint8_t v___x_3064_; 
v_lctx_3063_ = lean_ctor_get(v_a_3024_, 2);
v___x_3064_ = l_Lean_LocalContext_usesUserName(v_lctx_3063_, v_snd_3062_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_snd_3062_);
return v___x_3065_;
}
else
{
lean_object* v___f_3066_; 
lean_inc(v_snd_3062_);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3066_, 0, v_snd_3062_);
if (v_preserveName_3020_ == 0)
{
v___y_3035_ = v_lctx_3063_;
v___y_3036_ = v___f_3066_;
v___y_3037_ = v_snd_3062_;
goto v___jp_3034_;
}
else
{
if (v_fst_3061_ == 0)
{
lean_object* v___x_3067_; 
lean_dec_ref(v___f_3066_);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_snd_3062_);
return v___x_3067_;
}
else
{
v___y_3035_ = v_lctx_3063_;
v___y_3036_ = v___f_3066_;
v___y_3037_ = v_snd_3062_;
goto v___jp_3034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3072_, lean_object* v_body_3073_, lean_object* v_preserveName_3074_, lean_object* v_avoid_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
uint8_t v_preserveName_boxed_3083_; lean_object* v_res_3084_; 
v_preserveName_boxed_3083_ = lean_unbox(v_preserveName_3074_);
v_res_3084_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3072_, v_body_3073_, v_preserveName_boxed_3083_, v_avoid_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_avoid_3075_);
lean_dec_ref(v_body_3073_);
lean_dec(v_suggestion_3072_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v_holeIter_3088_; lean_object* v_curr_3089_; lean_object* v___x_3090_; lean_object* v_steps_3091_; lean_object* v_infos_3092_; lean_object* v_holeIter_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3103_; 
v___x_3087_ = lean_st_ref_get(v___y_3085_);
v_holeIter_3088_ = lean_ctor_get(v___x_3087_, 2);
lean_inc_ref(v_holeIter_3088_);
lean_dec(v___x_3087_);
v_curr_3089_ = lean_ctor_get(v_holeIter_3088_, 0);
lean_inc(v_curr_3089_);
lean_dec_ref(v_holeIter_3088_);
v___x_3090_ = lean_st_ref_take(v___y_3085_);
v_steps_3091_ = lean_ctor_get(v___x_3090_, 0);
v_infos_3092_ = lean_ctor_get(v___x_3090_, 1);
v_holeIter_3093_ = lean_ctor_get(v___x_3090_, 2);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3095_ = v___x_3090_;
v_isShared_3096_ = v_isSharedCheck_3103_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_holeIter_3093_);
lean_inc(v_infos_3092_);
lean_inc(v_steps_3091_);
lean_dec(v___x_3090_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3103_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 2, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_steps_3091_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_infos_3092_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_st_ref_put(v___y_3085_, v___x_3099_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_curr_3089_);
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3104_);
lean_dec(v___y_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3108_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3123_, lean_object* v_e_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3132_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3126_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc_n(v_a_3133_, 2);
lean_dec_ref(v___x_3132_);
v___x_3134_ = l_Lean_mkIdent(v_n_3123_);
v___x_3135_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3133_, v___x_3134_);
v___x_3136_ = 0;
lean_inc(v___x_3135_);
v___x_3137_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3133_, v___x_3135_, v_e_3124_, v___x_3136_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v___x_3137_, 0);
lean_dec(v_unused_3145_);
v___x_3139_ = v___x_3137_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_dec(v___x_3137_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3135_);
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3135_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v___x_3135_);
v_a_3146_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3137_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3137_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3154_, lean_object* v_e_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3154_, v_e_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3164_, lean_object* v_x_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
v___x_3173_ = lean_apply_8(v_d_3164_, v_x_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, lean_box(0));
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3174_, v_x_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v_b_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; 
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
v___x_3193_ = lean_apply_8(v_k_3184_, v_b_3187_, v___y_3185_, v___y_3186_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, lean_box(0));
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v_b_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3194_, v___y_3195_, v___y_3196_, v_b_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3204_, uint8_t v_bi_3205_, lean_object* v_type_3206_, lean_object* v_k_3207_, uint8_t v_kind_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; 
lean_inc(v___y_3210_);
lean_inc_ref(v___y_3209_);
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3216_, 0, v_k_3207_);
lean_closure_set(v___f_3216_, 1, v___y_3209_);
lean_closure_set(v___f_3216_, 2, v___y_3210_);
v___x_3217_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3204_, v_bi_3205_, v_type_3206_, v___f_3216_, v_kind_3208_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3217_) == 0)
{
return v___x_3217_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3226_, lean_object* v_bi_3227_, lean_object* v_type_3228_, lean_object* v_k_3229_, lean_object* v_kind_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_bi_boxed_3238_; uint8_t v_kind_boxed_3239_; lean_object* v_res_3240_; 
v_bi_boxed_3238_ = lean_unbox(v_bi_3227_);
v_kind_boxed_3239_ = lean_unbox(v_kind_3230_);
v_res_3240_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3226_, v_bi_boxed_3238_, v_type_3228_, v_k_3229_, v_kind_boxed_3239_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3241_, lean_object* v_childIdx_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_subExpr_3251_; lean_object* v_optionsPerPos_3252_; lean_object* v_currNamespace_3253_; lean_object* v_openDecls_3254_; uint8_t v_inPattern_3255_; lean_object* v_depth_3256_; lean_object* v_lctxInitIndices_3257_; lean_object* v_pos_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_subExpr_3251_ = lean_ctor_get(v___y_3244_, 3);
v_optionsPerPos_3252_ = lean_ctor_get(v___y_3244_, 0);
v_currNamespace_3253_ = lean_ctor_get(v___y_3244_, 1);
v_openDecls_3254_ = lean_ctor_get(v___y_3244_, 2);
v_inPattern_3255_ = lean_ctor_get_uint8(v___y_3244_, sizeof(void*)*6);
v_depth_3256_ = lean_ctor_get(v___y_3244_, 4);
v_lctxInitIndices_3257_ = lean_ctor_get(v___y_3244_, 5);
v_pos_3258_ = lean_ctor_get(v_subExpr_3251_, 1);
v___x_3259_ = l_Lean_SubExpr_Pos_push(v_pos_3258_, v_childIdx_3242_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v_child_3241_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
lean_inc(v_lctxInitIndices_3257_);
lean_inc(v_depth_3256_);
lean_inc(v_openDecls_3254_);
lean_inc(v_currNamespace_3253_);
lean_inc(v_optionsPerPos_3252_);
v___x_3261_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3261_, 0, v_optionsPerPos_3252_);
lean_ctor_set(v___x_3261_, 1, v_currNamespace_3253_);
lean_ctor_set(v___x_3261_, 2, v_openDecls_3254_);
lean_ctor_set(v___x_3261_, 3, v___x_3260_);
lean_ctor_set(v___x_3261_, 4, v_depth_3256_);
lean_ctor_set(v___x_3261_, 5, v_lctxInitIndices_3257_);
lean_ctor_set_uint8(v___x_3261_, sizeof(void*)*6, v_inPattern_3255_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3262_ = lean_apply_7(v_x_3243_, v___x_3261_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, lean_box(0));
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3263_, lean_object* v_childIdx_3264_, lean_object* v_x_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3263_, v_childIdx_3264_, v_x_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3274_, lean_object* v_a_3275_, lean_object* v_x_3276_, lean_object* v_fvar_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc_ref(v_fvar_3277_);
v___x_3285_ = lean_apply_8(v_v_3274_, v_fvar_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, lean_box(0));
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = l_Lean_Expr_bindingBody_x21(v_a_3275_);
v___x_3288_ = lean_expr_instantiate1(v___x_3287_, v_fvar_3277_);
lean_dec_ref(v_fvar_3277_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = lean_unsigned_to_nat(1u);
v___x_3290_ = lean_apply_1(v_x_3276_, v_a_3286_);
v___x_3291_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3288_, v___x_3289_, v___x_3290_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec_ref(v_fvar_3277_);
lean_dec_ref(v_x_3276_);
v_a_3292_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3285_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3285_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3300_, lean_object* v_a_3301_, lean_object* v_x_3302_, lean_object* v_fvar_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3300_, v_a_3301_, v_x_3302_, v_fvar_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v_a_3301_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3312_, lean_object* v_v_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3322_; lean_object* v_a_3323_; lean_object* v___f_3324_; uint8_t v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3322_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3315_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc_n(v_a_3323_, 2);
lean_dec_ref(v___x_3322_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3324_, 0, v_v_3313_);
lean_closure_set(v___f_3324_, 1, v_a_3323_);
lean_closure_set(v___f_3324_, 2, v_x_3314_);
v___x_3325_ = l_Lean_Expr_binderInfo(v_a_3323_);
v___x_3326_ = l_Lean_Expr_bindingDomain_x21(v_a_3323_);
lean_dec(v_a_3323_);
v___x_3327_ = 0;
v___x_3328_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3312_, v___x_3325_, v___x_3326_, v___f_3324_, v___x_3327_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3329_, lean_object* v_v_3330_, lean_object* v_x_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3329_, v_v_3330_, v_x_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3340_, uint8_t v_preserveName_3341_, lean_object* v_avoid_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v_a_3352_; lean_object* v___x_3353_; lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3350_, 0, v_d_3340_);
v___x_3351_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3343_);
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3343_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___x_3353_);
v___x_3355_ = l_Lean_Expr_bindingName_x21(v_a_3352_);
lean_dec(v_a_3352_);
v___x_3356_ = l_Lean_Expr_bindingBody_x21(v_a_3354_);
lean_dec(v_a_3354_);
v___x_3357_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3355_, v___x_3356_, v_preserveName_3341_, v_avoid_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec_ref(v___x_3356_);
lean_dec(v___x_3355_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_n(v_a_3358_, 2);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3359_, 0, v_a_3358_);
v___x_3360_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3358_, v___x_3359_, v___f_3350_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
return v___x_3360_;
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v___f_3350_);
v_a_3361_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3357_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3369_, lean_object* v_preserveName_3370_, lean_object* v_avoid_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
uint8_t v_preserveName_boxed_3379_; lean_object* v_res_3380_; 
v_preserveName_boxed_3379_ = lean_unbox(v_preserveName_3370_);
v_res_3380_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3369_, v_preserveName_boxed_3379_, v_avoid_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_avoid_3371_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3381_, lean_object* v_d_3382_, uint8_t v_preserveName_3383_, lean_object* v_avoid_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3382_, v_preserveName_3383_, v_avoid_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_d_3394_, lean_object* v_preserveName_3395_, lean_object* v_avoid_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
uint8_t v_preserveName_boxed_3404_; lean_object* v_res_3405_; 
v_preserveName_boxed_3404_ = lean_unbox(v_preserveName_3395_);
v_res_3405_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3393_, v_d_3394_, v_preserveName_boxed_3404_, v_avoid_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_avoid_3396_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3406_, lean_object* v_child_3407_, lean_object* v_childIdx_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3407_, v_childIdx_3408_, v_x_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_child_3419_, lean_object* v_childIdx_3420_, lean_object* v_x_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3418_, v_child_3419_, v_childIdx_3420_, v_x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3430_, lean_object* v_name_3431_, uint8_t v_bi_3432_, lean_object* v_type_3433_, lean_object* v_k_3434_, uint8_t v_kind_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3431_, v_bi_3432_, v_type_3433_, v_k_3434_, v_kind_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_name_3445_, lean_object* v_bi_3446_, lean_object* v_type_3447_, lean_object* v_k_3448_, lean_object* v_kind_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
uint8_t v_bi_boxed_3457_; uint8_t v_kind_boxed_3458_; lean_object* v_res_3459_; 
v_bi_boxed_3457_ = lean_unbox(v_bi_3446_);
v_kind_boxed_3458_ = lean_unbox(v_kind_3449_);
v_res_3459_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3444_, v_name_3445_, v_bi_boxed_3457_, v_type_3447_, v_k_3448_, v_kind_boxed_3458_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3460_, lean_object* v_00_u03b2_3461_, lean_object* v_n_3462_, lean_object* v_v_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3462_, v_v_3463_, v_x_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3473_, lean_object* v_00_u03b2_3474_, lean_object* v_n_3475_, lean_object* v_v_3476_, lean_object* v_x_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3473_, v_00_u03b2_3474_, v_n_3475_, v_v_3476_, v_x_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(lean_object* v_x_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_obj_tag_nat(v_x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl___boxed(lean_object* v_x_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(v_x_3488_);
lean_dec(v_x_3488_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3490_, lean_object* v_k_3491_){
_start:
{
if (lean_obj_tag(v_t_3490_) == 3)
{
lean_object* v_s_3492_; lean_object* v___x_3493_; 
v_s_3492_ = lean_ctor_get(v_t_3490_, 0);
lean_inc_ref(v_s_3492_);
lean_dec_ref_known(v_t_3490_, 1);
v___x_3493_ = lean_apply_1(v_k_3491_, v_s_3492_);
return v___x_3493_;
}
else
{
lean_dec(v_t_3490_);
return v_k_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3494_, lean_object* v_ctorIdx_3495_, lean_object* v_t_3496_, lean_object* v_h_3497_, lean_object* v_k_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3496_, v_k_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3500_, lean_object* v_ctorIdx_3501_, lean_object* v_t_3502_, lean_object* v_h_3503_, lean_object* v_k_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3500_, v_ctorIdx_3501_, v_t_3502_, v_h_3503_, v_k_3504_);
lean_dec(v_ctorIdx_3501_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3506_, lean_object* v_deep_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3506_, v_deep_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3509_, lean_object* v_t_3510_, lean_object* v_h_3511_, lean_object* v_deep_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3510_, v_deep_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3514_, lean_object* v_proof_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3514_, v_proof_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3517_, lean_object* v_t_3518_, lean_object* v_h_3519_, lean_object* v_proof_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3518_, v_proof_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3522_, lean_object* v_maxSteps_3523_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3522_, v_maxSteps_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3525_, lean_object* v_t_3526_, lean_object* v_h_3527_, lean_object* v_maxSteps_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3526_, v_maxSteps_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3530_, lean_object* v_string_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3530_, v_string_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3533_, lean_object* v_t_3534_, lean_object* v_h_3535_, lean_object* v_string_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3534_, v_string_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3541_){
_start:
{
switch(lean_obj_tag(v_x_3541_))
{
case 0:
{
lean_object* v___x_3542_; 
v___x_3542_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3542_;
}
case 1:
{
lean_object* v___x_3543_; 
v___x_3543_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3543_;
}
case 2:
{
lean_object* v___x_3544_; 
v___x_3544_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3544_;
}
default: 
{
lean_object* v_s_3545_; 
v_s_3545_ = lean_ctor_get(v_x_3541_, 0);
lean_inc_ref(v_s_3545_);
return v_s_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3546_);
lean_dec(v_x_3546_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3548_, lean_object* v_stx_3549_, lean_object* v_e_3550_, lean_object* v_reason_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3555_ = 0;
v___x_3556_ = lean_box(0);
v___x_3557_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3551_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
v___x_3559_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3548_, v_stx_3549_, v_e_3550_, v___x_3555_, v___x_3556_, v___x_3558_, v___x_3556_, v___x_3555_, v_a_3552_, v_a_3553_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3560_, lean_object* v_stx_3561_, lean_object* v_e_3562_, lean_object* v_reason_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3560_, v_stx_3561_, v_e_3562_, v_reason_3563_, v_a_3564_, v_a_3565_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec(v_reason_3563_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3568_, lean_object* v_stx_3569_, lean_object* v_e_3570_, lean_object* v_reason_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3568_, v_stx_3569_, v_e_3570_, v_reason_3571_, v_a_3573_, v_a_3574_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3580_, lean_object* v_stx_3581_, lean_object* v_e_3582_, lean_object* v_reason_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3580_, v_stx_3581_, v_e_3582_, v_reason_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_reason_3583_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3592_, lean_object* v_ctx_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_optionsPerPos_3600_; lean_object* v_currNamespace_3601_; lean_object* v_openDecls_3602_; uint8_t v_inPattern_3603_; lean_object* v_subExpr_3604_; lean_object* v_depth_3605_; lean_object* v_lctxInitIndices_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_optionsPerPos_3600_ = lean_ctor_get(v_ctx_3593_, 0);
v_currNamespace_3601_ = lean_ctor_get(v_ctx_3593_, 1);
v_openDecls_3602_ = lean_ctor_get(v_ctx_3593_, 2);
v_inPattern_3603_ = lean_ctor_get_uint8(v_ctx_3593_, sizeof(void*)*6);
v_subExpr_3604_ = lean_ctor_get(v_ctx_3593_, 3);
v_depth_3605_ = lean_ctor_get(v_ctx_3593_, 4);
v_lctxInitIndices_3606_ = lean_ctor_get(v_ctx_3593_, 5);
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = lean_nat_add(v_depth_3605_, v___x_3607_);
lean_inc(v_lctxInitIndices_3606_);
lean_inc_ref(v_subExpr_3604_);
lean_inc(v_openDecls_3602_);
lean_inc(v_currNamespace_3601_);
lean_inc(v_optionsPerPos_3600_);
v___x_3609_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3609_, 0, v_optionsPerPos_3600_);
lean_ctor_set(v___x_3609_, 1, v_currNamespace_3601_);
lean_ctor_set(v___x_3609_, 2, v_openDecls_3602_);
lean_ctor_set(v___x_3609_, 3, v_subExpr_3604_);
lean_ctor_set(v___x_3609_, 4, v___x_3608_);
lean_ctor_set(v___x_3609_, 5, v_lctxInitIndices_3606_);
lean_ctor_set_uint8(v___x_3609_, sizeof(void*)*6, v_inPattern_3603_);
lean_inc(v_a_3598_);
lean_inc_ref(v_a_3597_);
lean_inc(v_a_3596_);
lean_inc_ref(v_a_3595_);
lean_inc(v_a_3594_);
v___x_3610_ = lean_apply_7(v_act_3592_, v___x_3609_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, lean_box(0));
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3611_, lean_object* v_ctx_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3611_, v_ctx_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec_ref(v_ctx_3612_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3620_, lean_object* v_act_3621_, lean_object* v_ctx_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3621_, v_ctx_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3630_, lean_object* v_act_3631_, lean_object* v_ctx_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3630_, v_act_3631_, v_ctx_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_ctx_3632_);
return v_res_3639_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3640_, lean_object* v_e_3641_){
_start:
{
lean_object* v___y_3643_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(254u);
v___x_3648_ = lean_nat_dec_le(v___x_3647_, v_threshold_3640_);
if (v___x_3648_ == 0)
{
v___y_3643_ = v_threshold_3640_;
goto v___jp_3642_;
}
else
{
v___y_3643_ = v___x_3647_;
goto v___jp_3642_;
}
v___jp_3642_:
{
uint32_t v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3644_ = l_Lean_Expr_approxDepth(v_e_3641_);
v___x_3645_ = lean_uint32_to_nat(v___x_3644_);
v___x_3646_ = lean_nat_dec_le(v___x_3645_, v___y_3643_);
lean_dec(v___x_3645_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3649_, lean_object* v_e_3650_){
_start:
{
uint8_t v_res_3651_; lean_object* v_r_3652_; 
v_res_3651_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3649_, v_e_3650_);
lean_dec_ref(v_e_3650_);
lean_dec(v_threshold_3649_);
v_r_3652_ = lean_box(v_res_3651_);
return v_r_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
uint8_t v___x_3663_; 
v___x_3663_ = l_Lean_Expr_isAtomic(v_e_3655_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3665_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3664_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3708_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3708_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3708_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_unbox(v_a_3666_);
if (v___x_3670_ == 0)
{
lean_object* v_depth_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_del_object(v___x_3668_);
v_depth_3671_ = lean_ctor_get(v_a_3656_, 4);
v___x_3672_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3673_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3672_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3695_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3695_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3695_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3678_ = lean_nat_sub(v_depth_3671_, v_a_3674_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_nat_dec_lt(v___x_3679_, v___x_3678_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v___x_3678_);
lean_dec(v_a_3674_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v_a_3666_);
v___x_3682_ = v___x_3676_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3666_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3684_ = lean_unsigned_to_nat(2u);
v___x_3685_ = lean_nat_shiftr(v_a_3674_, v___x_3684_);
lean_dec(v_a_3674_);
v___x_3686_ = lean_nat_sub(v___x_3685_, v___x_3678_);
lean_dec(v___x_3678_);
lean_dec(v___x_3685_);
v___x_3687_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3686_, v_e_3655_);
lean_dec(v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_dec(v_a_3666_);
v___x_3688_ = lean_box(v___x_3680_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3688_);
v___x_3690_ = v___x_3676_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
else
{
lean_object* v___x_3693_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v_a_3666_);
v___x_3693_ = v___x_3676_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3666_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3666_);
v_a_3696_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3673_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3673_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec(v_a_3666_);
v___x_3704_ = lean_box(v___x_3663_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3704_);
v___x_3706_ = v___x_3668_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
return v___x_3665_;
}
}
else
{
uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = 0;
v___x_3710_ = lean_box(v___x_3709_);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec_ref(v_e_3712_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
uint8_t v___x_3731_; 
v___x_3731_ = l_Lean_Expr_isAtomic(v_e_3723_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3733_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3732_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3783_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3783_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3783_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___y_3739_; uint8_t v___x_3764_; 
v___x_3764_ = lean_unbox(v_a_3734_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; 
lean_del_object(v___x_3736_);
lean_inc_ref(v_e_3723_);
v___x_3765_ = l_Lean_Meta_isProof(v_e_3723_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3765_) == 0)
{
v___y_3739_ = v___x_3765_;
goto v___jp_3738_;
}
else
{
lean_object* v_a_3766_; uint8_t v___y_3768_; uint8_t v___x_3777_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v___x_3777_ = l_Lean_Exception_isInterrupt(v_a_3766_);
if (v___x_3777_ == 0)
{
uint8_t v___x_3778_; 
lean_inc(v_a_3766_);
v___x_3778_ = l_Lean_Exception_isRuntime(v_a_3766_);
v___y_3768_ = v___x_3778_;
goto v___jp_3767_;
}
else
{
v___y_3768_ = v___x_3777_;
goto v___jp_3767_;
}
v___jp_3767_:
{
if (v___y_3768_ == 0)
{
lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_e_3723_);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___x_3765_, 0);
lean_dec(v_unused_3776_);
v___x_3770_ = v___x_3765_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v___x_3765_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 0);
lean_ctor_set(v___x_3770_, 0, v_a_3734_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3734_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
v___y_3739_ = v___x_3765_;
goto v___jp_3738_;
}
}
}
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3781_; 
lean_dec(v_a_3734_);
lean_dec_ref(v_e_3723_);
v___x_3779_ = lean_box(v___x_3731_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3779_);
v___x_3781_ = v___x_3736_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
v___jp_3738_:
{
if (lean_obj_tag(v___y_3739_) == 0)
{
lean_object* v_a_3740_; uint8_t v___x_3741_; 
v_a_3740_ = lean_ctor_get(v___y_3739_, 0);
v___x_3741_ = lean_unbox(v_a_3740_);
if (v___x_3741_ == 0)
{
lean_dec(v_a_3734_);
lean_dec_ref(v_e_3723_);
return v___y_3739_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_inc(v_a_3740_);
lean_dec_ref_known(v___y_3739_, 1);
v___x_3742_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3743_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3742_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3755_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3755_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3755_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
uint8_t v___x_3748_; 
v___x_3748_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3744_, v_e_3723_);
lean_dec_ref(v_e_3723_);
lean_dec(v_a_3744_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3750_; 
lean_dec(v_a_3734_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v_a_3740_);
v___x_3750_ = v___x_3746_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3740_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
else
{
lean_object* v___x_3753_; 
lean_dec(v_a_3740_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v_a_3734_);
v___x_3753_ = v___x_3746_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3734_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v_a_3740_);
lean_dec(v_a_3734_);
lean_dec_ref(v_e_3723_);
v_a_3756_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3743_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3743_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
else
{
lean_dec(v_a_3734_);
lean_dec_ref(v_e_3723_);
return v___y_3739_;
}
}
}
}
else
{
lean_dec_ref(v_e_3723_);
return v___x_3733_;
}
}
else
{
uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec_ref(v_e_3723_);
v___x_3784_ = 0;
v___x_3785_ = lean_box(v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
return v___x_3786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_ref_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_ref_3810_ = lean_ctor_get(v_a_3808_, 2);
v___x_3811_ = 0;
v___x_3812_ = l_Lean_SourceInfo_fromRef(v_ref_3810_, v___x_3811_);
v___x_3813_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3814_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3812_);
v___x_3815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3812_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = l_Lean_Syntax_node1(v___x_3812_, v___x_3813_, v___x_3815_);
v___x_3817_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3816_, v_a_3805_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v_a_3822_; lean_object* v___x_3823_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_n(v_a_3818_, 2);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3805_);
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3805_);
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3820_, v_a_3818_, v_a_3822_, v_reason_3804_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v___x_3823_, 0);
lean_dec(v_unused_3831_);
v___x_3825_ = v___x_3823_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v___x_3823_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_a_3818_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3818_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v_a_3818_);
v_a_3832_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3823_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3823_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
return v___x_3817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
lean_dec_ref(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_reason_3840_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3852_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_reason_3856_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
if (lean_obj_tag(v_x_3865_) == 0)
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3873_;
}
else
{
lean_object* v_head_3874_; lean_object* v_tail_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_head_3874_ = lean_ctor_get(v_x_3865_, 0);
lean_inc(v_head_3874_);
v_tail_3875_ = lean_ctor_get(v_x_3865_, 1);
lean_inc(v_tail_3875_);
lean_dec_ref_known(v_x_3865_, 2);
v___x_3876_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
lean_inc(v___y_3867_);
lean_inc_ref(v___y_3866_);
v___x_3877_ = lean_apply_7(v_head_3874_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, lean_box(0));
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_dec(v_tail_3875_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; uint8_t v___y_3880_; uint8_t v___x_3884_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
v___x_3884_ = l_Lean_Exception_isInterrupt(v_a_3878_);
if (v___x_3884_ == 0)
{
uint8_t v___x_3885_; 
lean_inc(v_a_3878_);
v___x_3885_ = l_Lean_Exception_isRuntime(v_a_3878_);
v___y_3880_ = v___x_3885_;
goto v___jp_3879_;
}
else
{
v___y_3880_ = v___x_3884_;
goto v___jp_3879_;
}
v___jp_3879_:
{
if (v___y_3880_ == 0)
{
if (lean_obj_tag(v_a_3878_) == 0)
{
lean_dec_ref_known(v_a_3878_, 2);
lean_dec(v_tail_3875_);
return v___x_3877_;
}
else
{
lean_object* v_id_3881_; uint8_t v___x_3882_; 
v_id_3881_ = lean_ctor_get(v_a_3878_, 0);
lean_inc(v_id_3881_);
lean_dec_ref_known(v_a_3878_, 2);
v___x_3882_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3876_, v_id_3881_);
lean_dec(v_id_3881_);
if (v___x_3882_ == 0)
{
lean_dec(v_tail_3875_);
return v___x_3877_;
}
else
{
lean_dec_ref_known(v___x_3877_, 1);
v_x_3865_ = v_tail_3875_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3878_);
lean_dec(v_tail_3875_);
return v___x_3877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
if (lean_obj_tag(v_x_3895_) == 0)
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v___y_3906_; lean_object* v___y_3907_; uint8_t v___y_3908_; lean_object* v___y_3916_; lean_object* v___x_3920_; lean_object* v_env_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3904_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3920_ = lean_st_ref_get(v_a_3901_);
v_env_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_env_3921_);
lean_dec(v___x_3920_);
v___x_3922_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3923_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3922_, v_env_3921_, v_x_3895_);
v___x_3924_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3923_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3925_, v_a_3896_, v_a_3897_, v_a_3898_);
v___y_3916_ = v___x_3926_;
goto v___jp_3915_;
}
else
{
v___y_3916_ = v___x_3924_;
goto v___jp_3915_;
}
v___jp_3905_:
{
if (v___y_3908_ == 0)
{
if (lean_obj_tag(v___y_3907_) == 0)
{
lean_dec_ref_known(v___y_3907_, 2);
lean_dec(v_x_3895_);
return v___y_3906_;
}
else
{
lean_object* v_id_3909_; uint8_t v___x_3910_; 
v_id_3909_ = lean_ctor_get(v___y_3907_, 0);
lean_inc(v_id_3909_);
lean_dec_ref_known(v___y_3907_, 2);
v___x_3910_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3904_, v_id_3909_);
lean_dec(v_id_3909_);
if (v___x_3910_ == 0)
{
lean_dec(v_x_3895_);
return v___y_3906_;
}
else
{
uint8_t v___x_3911_; 
lean_dec_ref(v___y_3906_);
v___x_3911_ = l_Lean_Name_isAtomic(v_x_3895_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_Name_getRoot(v_x_3895_);
lean_dec(v_x_3895_);
v_x_3895_ = v___x_3912_;
goto _start;
}
else
{
lean_object* v___x_3914_; 
lean_dec(v_x_3895_);
v___x_3914_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3914_;
}
}
}
}
else
{
lean_dec_ref(v___y_3907_);
lean_dec(v_x_3895_);
return v___y_3906_;
}
}
v___jp_3915_:
{
if (lean_obj_tag(v___y_3916_) == 0)
{
lean_dec(v_x_3895_);
return v___y_3916_;
}
else
{
lean_object* v_a_3917_; uint8_t v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___y_3916_, 0);
lean_inc(v_a_3917_);
v___x_3918_ = l_Lean_Exception_isInterrupt(v_a_3917_);
if (v___x_3918_ == 0)
{
uint8_t v___x_3919_; 
lean_inc(v_a_3917_);
v___x_3919_ = l_Lean_Exception_isRuntime(v_a_3917_);
v___y_3906_ = v___y_3916_;
v___y_3907_ = v_a_3917_;
v___y_3908_ = v___x_3919_;
goto v___jp_3905_;
}
else
{
v___y_3906_ = v___y_3916_;
v___y_3907_ = v_a_3917_;
v___y_3908_ = v___x_3918_;
goto v___jp_3905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; lean_object* v_env_3943_; uint8_t v___x_3944_; lean_object* v_env_3945_; lean_object* v___x_3946_; lean_object* v_toCold_3947_; lean_object* v_mctx_3948_; lean_object* v_lctx_3949_; lean_object* v_options_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3942_ = lean_st_ref_get(v___y_3940_);
v_env_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc_ref(v_env_3943_);
lean_dec(v___x_3942_);
v___x_3944_ = 0;
v_env_3945_ = l_Lean_Environment_setRecordingDeps(v_env_3943_, v___x_3944_);
v___x_3946_ = lean_st_ref_get(v___y_3938_);
v_toCold_3947_ = lean_ctor_get(v___y_3939_, 0);
v_mctx_3948_ = lean_ctor_get(v___x_3946_, 0);
lean_inc_ref(v_mctx_3948_);
lean_dec(v___x_3946_);
v_lctx_3949_ = lean_ctor_get(v___y_3937_, 2);
v_options_3950_ = lean_ctor_get(v_toCold_3947_, 2);
lean_inc_ref(v_options_3950_);
lean_inc_ref(v_lctx_3949_);
v___x_3951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3951_, 0, v_env_3945_);
lean_ctor_set(v___x_3951_, 1, v_mctx_3948_);
lean_ctor_set(v___x_3951_, 2, v_lctx_3949_);
lean_ctor_set(v___x_3951_, 3, v_options_3950_);
v___x_3952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v_msgData_3936_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_ref_3967_; lean_object* v___x_3968_; lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3977_; 
v_ref_3967_ = lean_ctor_get(v___y_3964_, 2);
v___x_3968_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
lean_inc(v_ref_3967_);
v___x_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_ref_3967_);
lean_ctor_set(v___x_3973_, 1, v_a_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 1);
lean_ctor_set(v___x_3971_, 0, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3984_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3987_ = l_Lean_stringToMessageData(v___x_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_3988_);
v___x_3997_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_dec(v_a_3988_);
return v___x_3997_;
}
else
{
lean_object* v_a_3998_; uint8_t v___y_4000_; uint8_t v___x_4016_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
v___x_4016_ = l_Lean_Exception_isInterrupt(v_a_3998_);
if (v___x_4016_ == 0)
{
uint8_t v___x_4017_; 
lean_inc(v_a_3998_);
v___x_4017_ = l_Lean_Exception_isRuntime(v_a_3998_);
v___y_4000_ = v___x_4017_;
goto v___jp_3999_;
}
else
{
v___y_4000_ = v___x_4016_;
goto v___jp_3999_;
}
v___jp_3999_:
{
if (v___y_4000_ == 0)
{
if (lean_obj_tag(v_a_3998_) == 0)
{
lean_dec_ref_known(v_a_3998_, 2);
lean_dec(v_a_3988_);
return v___x_3997_;
}
else
{
lean_object* v_id_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4014_; 
v_id_4001_ = lean_ctor_get(v_a_3998_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_a_3998_);
if (v_isSharedCheck_4014_ == 0)
{
lean_object* v_unused_4015_; 
v_unused_4015_ = lean_ctor_get(v_a_3998_, 1);
lean_dec(v_unused_4015_);
v___x_4003_ = v_a_3998_;
v_isShared_4004_ = v_isSharedCheck_4014_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_id_4001_);
lean_dec(v_a_3998_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4014_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
uint8_t v___x_4005_; 
v___x_4005_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3996_, v_id_4001_);
lean_dec(v_id_4001_);
if (v___x_4005_ == 0)
{
lean_del_object(v___x_4003_);
lean_dec(v_a_3988_);
return v___x_3997_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
lean_dec_ref_known(v___x_3997_, 1);
v___x_4006_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_4007_ = l_Lean_MessageData_ofName(v_a_3988_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 7);
lean_ctor_set(v___x_4003_, 1, v___x_4007_);
lean_ctor_set(v___x_4003_, 0, v___x_4006_);
v___x_4009_ = v___x_4003_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_4011_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v___x_4012_;
}
}
}
}
}
else
{
lean_dec(v_a_3998_);
lean_dec(v_a_3988_);
return v___x_3997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v_a_4036_; lean_object* v___x_4037_; 
v___x_4035_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4028_);
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref(v___x_4035_);
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
v___x_4037_ = lean_infer_type(v_a_4036_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___x_4039_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4040_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4038_, v___x_4039_, v_x_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
return v___x_4040_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v_x_4027_);
v_a_4041_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4037_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4037_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
return v_res_4057_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4076_ = l_String_toRawSubstring_x27(v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4135_ = l_Lean_Core_checkSystem(v___x_4134_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec_ref_known(v___x_4135_, 1);
v___x_4136_ = lean_st_ref_get(v_a_4128_);
v___x_4137_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4138_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4137_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v_steps_4140_; uint8_t v___x_4141_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v_steps_4140_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_steps_4140_);
lean_dec(v___x_4136_);
v___x_4141_ = lean_nat_dec_le(v_a_4139_, v_steps_4140_);
lean_dec(v_steps_4140_);
lean_dec(v_a_4139_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v_steps_4143_; lean_object* v_infos_4144_; lean_object* v_holeIter_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4318_; 
v___x_4142_ = lean_st_ref_take(v_a_4128_);
v_steps_4143_ = lean_ctor_get(v___x_4142_, 0);
v_infos_4144_ = lean_ctor_get(v___x_4142_, 1);
v_holeIter_4145_ = lean_ctor_get(v___x_4142_, 2);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4147_ = v___x_4142_;
v_isShared_4148_ = v_isSharedCheck_4318_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_holeIter_4145_);
lean_inc(v_infos_4144_);
lean_inc(v_steps_4143_);
lean_dec(v___x_4142_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4318_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4149_ = lean_unsigned_to_nat(1u);
v___x_4150_ = lean_nat_add(v_steps_4143_, v___x_4149_);
lean_dec(v_steps_4143_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4150_);
v___x_4152_ = v___x_4147_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_infos_4144_);
lean_ctor_set(v_reuseFailAlloc_4317_, 2, v_holeIter_4145_);
v___x_4152_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4153_ = lean_st_ref_put(v_a_4128_, v___x_4152_);
v___x_4154_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4127_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4155_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; uint8_t v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = lean_unbox(v_a_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; 
lean_inc(v_a_4155_);
v___x_4159_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4155_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; uint8_t v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = lean_unbox(v_a_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; 
lean_dec(v_a_4157_);
v___x_4162_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4164_, 0, v_a_4163_);
v___x_4165_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4164_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___y_4168_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4215_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4216_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4215_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; uint8_t v___x_4218_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v___x_4218_ = lean_unbox(v_a_4217_);
if (v___x_4218_ == 0)
{
lean_dec(v_a_4155_);
v___y_4168_ = v___x_4216_;
goto v___jp_4167_;
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_dec_ref_known(v___x_4216_, 1);
v___x_4219_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4220_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4219_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; uint8_t v___x_4222_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v___x_4222_ = lean_unbox(v_a_4221_);
if (v___x_4222_ == 0)
{
lean_dec(v_a_4155_);
v___y_4168_ = v___x_4220_;
goto v___jp_4167_;
}
else
{
uint8_t v___x_4223_; 
v___x_4223_ = l_Lean_Expr_isMData(v_a_4155_);
lean_dec(v_a_4155_);
if (v___x_4223_ == 0)
{
v___y_4168_ = v___x_4220_;
goto v___jp_4167_;
}
else
{
lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4160_);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4230_ == 0)
{
lean_object* v_unused_4231_; 
v_unused_4231_ = lean_ctor_get(v___x_4220_, 0);
lean_dec(v_unused_4231_);
v___x_4225_ = v___x_4220_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_dec(v___x_4220_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v_a_4166_);
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4166_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
else
{
lean_dec(v_a_4155_);
v___y_4168_ = v___x_4220_;
goto v___jp_4167_;
}
}
}
else
{
lean_dec(v_a_4155_);
v___y_4168_ = v___x_4216_;
goto v___jp_4167_;
}
v___jp_4167_:
{
if (lean_obj_tag(v___y_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4206_; 
v_a_4169_ = lean_ctor_get(v___y_4168_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___y_4168_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4171_ = v___y_4168_;
v_isShared_4172_ = v_isSharedCheck_4206_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___y_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4206_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_unbox(v_a_4169_);
lean_dec(v_a_4169_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4175_; 
lean_dec(v_a_4160_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 0, v_a_4166_);
v___x_4175_ = v___x_4171_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4166_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_del_object(v___x_4171_);
v___x_4177_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4178_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4177_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_toCold_4179_; lean_object* v_a_4180_; lean_object* v_ref_4181_; lean_object* v_quotContext_4182_; lean_object* v_currMacroScope_4183_; uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_toCold_4179_ = lean_ctor_get(v_a_4131_, 0);
v_a_4180_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4178_, 1);
v_ref_4181_ = lean_ctor_get(v_a_4131_, 2);
v_quotContext_4182_ = lean_ctor_get(v_toCold_4179_, 8);
v_currMacroScope_4183_ = lean_ctor_get(v_toCold_4179_, 9);
v___x_4184_ = lean_unbox(v_a_4160_);
lean_dec(v_a_4160_);
v___x_4185_ = l_Lean_SourceInfo_fromRef(v_ref_4181_, v___x_4184_);
v___x_4186_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4187_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4188_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4185_, 7);
v___x_4189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4185_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4191_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4192_ = lean_box(0);
lean_inc(v_currMacroScope_4183_);
lean_inc(v_quotContext_4182_);
v___x_4193_ = l_Lean_addMacroScope(v_quotContext_4182_, v___x_4192_, v_currMacroScope_4183_);
v___x_4194_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4185_);
lean_ctor_set(v___x_4195_, 1, v___x_4191_);
lean_ctor_set(v___x_4195_, 2, v___x_4193_);
lean_ctor_set(v___x_4195_, 3, v___x_4194_);
v___x_4196_ = l_Lean_Syntax_node1(v___x_4185_, v___x_4190_, v___x_4195_);
v___x_4197_ = l_Lean_Syntax_node2(v___x_4185_, v___x_4187_, v___x_4189_, v___x_4196_);
v___x_4198_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4185_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4201_ = l_Lean_Syntax_node1(v___x_4185_, v___x_4200_, v_a_4180_);
v___x_4202_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4185_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = l_Lean_Syntax_node5(v___x_4185_, v___x_4186_, v___x_4197_, v_a_4166_, v___x_4199_, v___x_4201_, v___x_4203_);
v___x_4205_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4204_, v_a_4127_);
return v___x_4205_;
}
else
{
lean_dec(v_a_4166_);
lean_dec(v_a_4160_);
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_a_4166_);
lean_dec(v_a_4160_);
v_a_4207_ = lean_ctor_get(v___y_4168_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___y_4168_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___y_4168_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___y_4168_);
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
else
{
lean_dec(v_a_4160_);
lean_dec(v_a_4155_);
return v___x_4165_;
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec(v_a_4160_);
lean_dec(v_a_4155_);
v_a_4232_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4162_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4162_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec(v_a_4160_);
lean_dec(v_a_4155_);
v___x_4240_ = lean_box(1);
v___x_4241_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4240_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4131_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4244_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4243_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4282_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4282_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4282_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_unbox(v_a_4245_);
lean_dec(v_a_4245_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4251_; 
lean_dec(v_a_4157_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v_a_4242_);
v___x_4251_ = v___x_4247_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4242_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
else
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
lean_del_object(v___x_4247_);
v___x_4253_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4254_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4253_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_toCold_4255_; lean_object* v_a_4256_; lean_object* v_ref_4257_; lean_object* v_quotContext_4258_; lean_object* v_currMacroScope_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_toCold_4255_ = lean_ctor_get(v_a_4131_, 0);
v_a_4256_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4254_, 1);
v_ref_4257_ = lean_ctor_get(v_a_4131_, 2);
v_quotContext_4258_ = lean_ctor_get(v_toCold_4255_, 8);
v_currMacroScope_4259_ = lean_ctor_get(v_toCold_4255_, 9);
v___x_4260_ = lean_unbox(v_a_4157_);
lean_dec(v_a_4157_);
v___x_4261_ = l_Lean_SourceInfo_fromRef(v_ref_4257_, v___x_4260_);
v___x_4262_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4263_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4264_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4261_, 7);
v___x_4265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4261_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4267_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4268_ = lean_box(0);
lean_inc(v_currMacroScope_4259_);
lean_inc(v_quotContext_4258_);
v___x_4269_ = l_Lean_addMacroScope(v_quotContext_4258_, v___x_4268_, v_currMacroScope_4259_);
v___x_4270_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4271_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4261_);
lean_ctor_set(v___x_4271_, 1, v___x_4267_);
lean_ctor_set(v___x_4271_, 2, v___x_4269_);
lean_ctor_set(v___x_4271_, 3, v___x_4270_);
v___x_4272_ = l_Lean_Syntax_node1(v___x_4261_, v___x_4266_, v___x_4271_);
v___x_4273_ = l_Lean_Syntax_node2(v___x_4261_, v___x_4263_, v___x_4265_, v___x_4272_);
v___x_4274_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4261_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4277_ = l_Lean_Syntax_node1(v___x_4261_, v___x_4276_, v_a_4256_);
v___x_4278_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4261_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = l_Lean_Syntax_node5(v___x_4261_, v___x_4262_, v___x_4273_, v_a_4242_, v___x_4275_, v___x_4277_, v___x_4279_);
v___x_4281_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4280_, v_a_4127_);
return v___x_4281_;
}
else
{
lean_dec(v_a_4242_);
lean_dec(v_a_4157_);
return v___x_4254_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_a_4242_);
lean_dec(v_a_4157_);
v_a_4283_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4244_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4244_);
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
lean_dec(v_a_4157_);
return v___x_4241_;
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v_a_4157_);
lean_dec(v_a_4155_);
v_a_4291_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4159_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4159_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_dec(v_a_4157_);
lean_dec(v_a_4155_);
v___x_4299_ = lean_box(0);
v___x_4300_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4299_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4131_);
return v___x_4300_;
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_a_4155_);
v_a_4301_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4156_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4156_);
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
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_a_4309_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4154_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4154_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_box(2);
v___x_4320_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4319_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4131_);
return v___x_4320_;
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v___x_4136_);
v_a_4321_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4138_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4138_);
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
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4329_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4135_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4135_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4337_, lean_object* v_msg_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4345_, lean_object* v_msg_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4345_, v_msg_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4353_, lean_object* v_x_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4363_, lean_object* v_x_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4363_, v_x_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4374_, lean_object* v_prec_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4384_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4383_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4397_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; lean_object* v_mctx_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4389_ = lean_st_ref_get(v_a_4379_);
v_mctx_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc_ref(v_mctx_4390_);
lean_dec(v___x_4389_);
v___x_4391_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4391_, 0, v_mctx_4390_);
v___x_4392_ = lean_unbox(v_a_4385_);
lean_dec(v_a_4385_);
v___x_4393_ = l_Lean_Level_quote(v_l_4374_, v_prec_4375_, v___x_4392_, v___x_4391_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4393_);
v___x_4395_ = v___x_4387_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v_l_4374_);
v_a_4398_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4384_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4384_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4406_, lean_object* v_prec_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4406_, v_prec_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_prec_4407_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4416_, lean_object* v_stx_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = lean_box(0);
v___x_4424_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4422_, v___x_4423_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; uint8_t v___x_4426_; lean_object* v___x_4427_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc_n(v_a_4425_, 2);
lean_dec_ref_known(v___x_4424_, 1);
v___x_4426_ = 0;
v___x_4427_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_a_4425_, v___x_4426_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4434_ == 0)
{
lean_object* v_unused_4435_; 
v_unused_4435_ = lean_ctor_get(v___x_4427_, 0);
lean_dec(v_unused_4435_);
v___x_4429_ = v___x_4427_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_dec(v___x_4427_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v_a_4425_);
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4425_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_a_4425_);
v_a_4436_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4427_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4427_);
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
else
{
return v___x_4424_;
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
v_a_4444_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4421_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4421_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4452_, lean_object* v_stx_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v_x_410__boxed_4457_; lean_object* v_res_4458_; 
v_x_410__boxed_4457_ = lean_unbox(v_x_4452_);
v_res_4458_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_410__boxed_4457_, v_stx_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4484_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4485_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4483_, v___x_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4491_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4492_ = l_Lean_addBuiltinDocString(v___x_4490_, v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4522_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4523_ = l_Lean_addBuiltinDeclarationRanges(v___x_4521_, v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v_mctx_4530_; lean_object* v___x_4531_; lean_object* v_fst_4532_; lean_object* v_snd_4533_; lean_object* v___x_4534_; lean_object* v_cache_4535_; lean_object* v_zetaDeltaFVarIds_4536_; lean_object* v_postponed_4537_; lean_object* v_diag_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4547_; 
v___x_4529_ = lean_st_ref_get(v___y_4527_);
v_mctx_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc_ref(v_mctx_4530_);
lean_dec(v___x_4529_);
v___x_4531_ = lean_instantiate_level_mvars(v_mctx_4530_, v_l_4526_);
v_fst_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_fst_4532_);
v_snd_4533_ = lean_ctor_get(v___x_4531_, 1);
lean_inc(v_snd_4533_);
lean_dec_ref(v___x_4531_);
v___x_4534_ = lean_st_ref_take(v___y_4527_);
v_cache_4535_ = lean_ctor_get(v___x_4534_, 1);
v_zetaDeltaFVarIds_4536_ = lean_ctor_get(v___x_4534_, 2);
v_postponed_4537_ = lean_ctor_get(v___x_4534_, 3);
v_diag_4538_ = lean_ctor_get(v___x_4534_, 4);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v___x_4534_, 0);
lean_dec(v_unused_4548_);
v___x_4540_ = v___x_4534_;
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_diag_4538_);
lean_inc(v_postponed_4537_);
lean_inc(v_zetaDeltaFVarIds_4536_);
lean_inc(v_cache_4535_);
lean_dec(v___x_4534_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v_fst_4532_);
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_fst_4532_);
lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_cache_4535_);
lean_ctor_set(v_reuseFailAlloc_4546_, 2, v_zetaDeltaFVarIds_4536_);
lean_ctor_set(v_reuseFailAlloc_4546_, 3, v_postponed_4537_);
lean_ctor_set(v_reuseFailAlloc_4546_, 4, v_diag_4538_);
v___x_4543_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = lean_st_ref_put(v___y_4527_, v___x_4543_);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_snd_4533_);
return v___x_4545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4549_, v___y_4550_);
lean_dec(v___y_4550_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4553_, v___y_4555_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4567_, lean_object* v_prec_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_l_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___x_4585_; uint8_t v___x_4586_; 
v___x_4585_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4571_);
v___x_4586_ = l_Lean_getPPInstantiateMVars(v___x_4585_);
lean_dec_ref(v___x_4585_);
if (v___x_4586_ == 0)
{
v_l_4575_ = v_l_4567_;
v___y_4576_ = v_a_4570_;
v___y_4577_ = v_a_4571_;
goto v___jp_4574_;
}
else
{
lean_object* v___x_4587_; lean_object* v_a_4588_; 
v___x_4587_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4567_, v_a_4570_);
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref(v___x_4587_);
v_l_4575_ = v_a_4588_;
v___y_4576_ = v_a_4570_;
v___y_4577_ = v_a_4571_;
goto v___jp_4574_;
}
v___jp_4574_:
{
lean_object* v___x_4578_; uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v_mctx_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4578_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4577_);
v___x_4579_ = l_Lean_getPPMVarsLevels(v___x_4578_);
lean_dec_ref(v___x_4578_);
v___x_4580_ = lean_st_ref_get(v___y_4576_);
v_mctx_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc_ref(v_mctx_4581_);
lean_dec(v___x_4580_);
v___x_4582_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4582_, 0, v_mctx_4581_);
v___x_4583_ = l_Lean_Level_quote(v_l_4575_, v_prec_4568_, v___x_4579_, v___x_4582_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4589_, lean_object* v_prec_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_PrettyPrinter_delabLevel(v_l_4589_, v_prec_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_prec_4590_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v___f_4604_; lean_object* v___x_8155__overap_4605_; lean_object* v___x_4606_; 
v___f_4604_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8155__overap_4605_ = lean_panic_fn_borrowed(v___f_4604_, v_msg_4598_);
lean_inc(v___y_4602_);
lean_inc_ref(v___y_4601_);
lean_inc(v___y_4600_);
lean_inc_ref(v___y_4599_);
v___x_4606_ = lean_apply_5(v___x_8155__overap_4605_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, lean_box(0));
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4614_, lean_object* v_msg_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4622_, lean_object* v_msg_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4622_, v_msg_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4630_, lean_object* v_opt_4631_){
_start:
{
lean_object* v_name_4632_; lean_object* v_defValue_4633_; lean_object* v_map_4634_; lean_object* v___x_4635_; 
v_name_4632_ = lean_ctor_get(v_opt_4631_, 0);
v_defValue_4633_ = lean_ctor_get(v_opt_4631_, 1);
v_map_4634_ = lean_ctor_get(v_opts_4630_, 0);
v___x_4635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4634_, v_name_4632_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_inc(v_defValue_4633_);
return v_defValue_4633_;
}
else
{
lean_object* v_val_4636_; 
v_val_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_val_4636_);
lean_dec_ref_known(v___x_4635_, 1);
if (lean_obj_tag(v_val_4636_) == 3)
{
lean_object* v_v_4637_; 
v_v_4637_ = lean_ctor_get(v_val_4636_, 0);
lean_inc(v_v_4637_);
lean_dec_ref_known(v_val_4636_, 1);
return v_v_4637_;
}
else
{
lean_dec(v_val_4636_);
lean_inc(v_defValue_4633_);
return v_defValue_4633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4638_, lean_object* v_opt_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4638_, v_opt_4639_);
lean_dec_ref(v_opt_4639_);
lean_dec_ref(v_opts_4638_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(lean_object* v_e_4641_, lean_object* v___y_4642_){
_start:
{
uint8_t v___x_4644_; 
v___x_4644_ = l_Lean_Expr_hasMVar(v_e_4641_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v_e_4641_);
return v___x_4645_;
}
else
{
lean_object* v___x_4646_; lean_object* v_mctx_4647_; lean_object* v___x_4648_; lean_object* v_fst_4649_; lean_object* v_snd_4650_; lean_object* v___x_4651_; lean_object* v_cache_4652_; lean_object* v_zetaDeltaFVarIds_4653_; lean_object* v_postponed_4654_; lean_object* v_diag_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4664_; 
v___x_4646_ = lean_st_ref_get(v___y_4642_);
v_mctx_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc_ref(v_mctx_4647_);
lean_dec(v___x_4646_);
v___x_4648_ = l_Lean_instantiateMVarsCore(v_mctx_4647_, v_e_4641_);
v_fst_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_fst_4649_);
v_snd_4650_ = lean_ctor_get(v___x_4648_, 1);
lean_inc(v_snd_4650_);
lean_dec_ref(v___x_4648_);
v___x_4651_ = lean_st_ref_take(v___y_4642_);
v_cache_4652_ = lean_ctor_get(v___x_4651_, 1);
v_zetaDeltaFVarIds_4653_ = lean_ctor_get(v___x_4651_, 2);
v_postponed_4654_ = lean_ctor_get(v___x_4651_, 3);
v_diag_4655_ = lean_ctor_get(v___x_4651_, 4);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4664_ == 0)
{
lean_object* v_unused_4665_; 
v_unused_4665_ = lean_ctor_get(v___x_4651_, 0);
lean_dec(v_unused_4665_);
v___x_4657_ = v___x_4651_;
v_isShared_4658_ = v_isSharedCheck_4664_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_diag_4655_);
lean_inc(v_postponed_4654_);
lean_inc(v_zetaDeltaFVarIds_4653_);
lean_inc(v_cache_4652_);
lean_dec(v___x_4651_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4664_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 0, v_snd_4650_);
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_snd_4650_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_cache_4652_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_zetaDeltaFVarIds_4653_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_postponed_4654_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_diag_4655_);
v___x_4660_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = lean_st_ref_put(v___y_4642_, v___x_4660_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_fst_4649_);
return v___x_4662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg___boxed(lean_object* v_e_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4666_, v___y_4667_);
lean_dec(v___y_4667_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_e_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4670_, v___y_4672_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_e_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(v_e_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4684_, lean_object* v_opt_4685_){
_start:
{
lean_object* v_name_4686_; lean_object* v_map_4687_; lean_object* v___x_4688_; 
v_name_4686_ = lean_ctor_get(v_opt_4685_, 0);
v_map_4687_ = lean_ctor_get(v_opts_4684_, 0);
v___x_4688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4687_, v_name_4686_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_box(0);
return v___x_4689_;
}
else
{
lean_object* v_val_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4700_; 
v_val_4690_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4692_ = v___x_4688_;
v_isShared_4693_ = v_isSharedCheck_4700_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_val_4690_);
lean_dec(v___x_4688_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4700_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
if (lean_obj_tag(v_val_4690_) == 1)
{
uint8_t v_v_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v_v_4694_ = lean_ctor_get_uint8(v_val_4690_, 0);
lean_dec_ref_known(v_val_4690_, 0);
v___x_4695_ = lean_box(v_v_4694_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v___x_4695_);
v___x_4697_ = v___x_4692_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
else
{
lean_object* v___x_4699_; 
lean_del_object(v___x_4692_);
lean_dec(v_val_4690_);
v___x_4699_ = lean_box(0);
return v___x_4699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4701_, lean_object* v_opt_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4701_, v_opt_4702_);
lean_dec_ref(v_opt_4702_);
lean_dec_ref(v_opts_4701_);
return v_res_4703_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_x_4704_, lean_object* v_x_4705_){
_start:
{
if (lean_obj_tag(v_x_4704_) == 0)
{
if (lean_obj_tag(v_x_4705_) == 0)
{
uint8_t v___x_4706_; 
v___x_4706_ = 1;
return v___x_4706_;
}
else
{
uint8_t v___x_4707_; 
v___x_4707_ = 0;
return v___x_4707_;
}
}
else
{
if (lean_obj_tag(v_x_4705_) == 0)
{
uint8_t v___x_4708_; 
v___x_4708_ = 0;
return v___x_4708_;
}
else
{
lean_object* v_val_4709_; uint8_t v___x_4710_; 
v_val_4709_ = lean_ctor_get(v_x_4705_, 0);
v___x_4710_ = lean_unbox(v_val_4709_);
if (v___x_4710_ == 0)
{
lean_object* v_val_4711_; uint8_t v___x_4712_; 
v_val_4711_ = lean_ctor_get(v_x_4704_, 0);
v___x_4712_ = lean_unbox(v_val_4711_);
if (v___x_4712_ == 0)
{
uint8_t v___x_4713_; 
v___x_4713_ = 1;
return v___x_4713_;
}
else
{
uint8_t v___x_4714_; 
v___x_4714_ = lean_unbox(v_val_4709_);
return v___x_4714_;
}
}
else
{
lean_object* v_val_4715_; uint8_t v___x_4716_; 
v_val_4715_ = lean_ctor_get(v_x_4704_, 0);
v___x_4716_ = lean_unbox(v_val_4715_);
return v___x_4716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_x_4717_, lean_object* v_x_4718_){
_start:
{
uint8_t v_res_4719_; lean_object* v_r_4720_; 
v_res_4719_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(v_x_4717_, v_x_4718_);
lean_dec(v_x_4718_);
lean_dec(v_x_4717_);
v_r_4720_ = lean_box(v_res_4719_);
return v_r_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_cls_4721_, lean_object* v_msg_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_ref_4728_; lean_object* v___x_4729_; lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4775_; 
v_ref_4728_ = lean_ctor_get(v___y_4725_, 2);
v___x_4729_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4775_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4775_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v_traceState_4735_; lean_object* v_env_4736_; lean_object* v_nextMacroScope_4737_; lean_object* v_ngen_4738_; lean_object* v_auxDeclNGen_4739_; lean_object* v_cache_4740_; lean_object* v_recordedDeps_4741_; lean_object* v_messages_4742_; lean_object* v_infoState_4743_; lean_object* v_snapshotTasks_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4774_; 
v___x_4734_ = lean_st_ref_take(v___y_4726_);
v_traceState_4735_ = lean_ctor_get(v___x_4734_, 4);
v_env_4736_ = lean_ctor_get(v___x_4734_, 0);
v_nextMacroScope_4737_ = lean_ctor_get(v___x_4734_, 1);
v_ngen_4738_ = lean_ctor_get(v___x_4734_, 2);
v_auxDeclNGen_4739_ = lean_ctor_get(v___x_4734_, 3);
v_cache_4740_ = lean_ctor_get(v___x_4734_, 5);
v_recordedDeps_4741_ = lean_ctor_get(v___x_4734_, 6);
v_messages_4742_ = lean_ctor_get(v___x_4734_, 7);
v_infoState_4743_ = lean_ctor_get(v___x_4734_, 8);
v_snapshotTasks_4744_ = lean_ctor_get(v___x_4734_, 9);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4746_ = v___x_4734_;
v_isShared_4747_ = v_isSharedCheck_4774_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_snapshotTasks_4744_);
lean_inc(v_infoState_4743_);
lean_inc(v_messages_4742_);
lean_inc(v_recordedDeps_4741_);
lean_inc(v_cache_4740_);
lean_inc(v_traceState_4735_);
lean_inc(v_auxDeclNGen_4739_);
lean_inc(v_ngen_4738_);
lean_inc(v_nextMacroScope_4737_);
lean_inc(v_env_4736_);
lean_dec(v___x_4734_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4774_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
uint64_t v_tid_4748_; lean_object* v_traces_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4773_; 
v_tid_4748_ = lean_ctor_get_uint64(v_traceState_4735_, sizeof(void*)*1);
v_traces_4749_ = lean_ctor_get(v_traceState_4735_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_traceState_4735_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4751_ = v_traceState_4735_;
v_isShared_4752_ = v_isSharedCheck_4773_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_traces_4749_);
lean_dec(v_traceState_4735_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4773_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; double v___x_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4753_ = lean_box(0);
v___x_4754_ = lean_box(0);
v___x_4755_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_4756_ = 0;
v___x_4757_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4758_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4758_, 0, v_cls_4721_);
lean_ctor_set(v___x_4758_, 1, v___x_4754_);
lean_ctor_set(v___x_4758_, 2, v___x_4757_);
lean_ctor_set_float(v___x_4758_, sizeof(void*)*3, v___x_4755_);
lean_ctor_set_float(v___x_4758_, sizeof(void*)*3 + 8, v___x_4755_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*3 + 16, v___x_4756_);
v___x_4759_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_4760_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set(v___x_4760_, 1, v_a_4730_);
lean_ctor_set(v___x_4760_, 2, v___x_4759_);
lean_inc(v_ref_4728_);
v___x_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4761_, 0, v_ref_4728_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = l_Lean_PersistentArray_push___redArg(v_traces_4749_, v___x_4761_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4762_);
v___x_4764_ = v___x_4751_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4762_);
lean_ctor_set_uint64(v_reuseFailAlloc_4772_, sizeof(void*)*1, v_tid_4748_);
v___x_4764_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4766_; 
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 4, v___x_4764_);
v___x_4766_ = v___x_4746_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_env_4736_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_nextMacroScope_4737_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_ngen_4738_);
lean_ctor_set(v_reuseFailAlloc_4771_, 3, v_auxDeclNGen_4739_);
lean_ctor_set(v_reuseFailAlloc_4771_, 4, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4771_, 5, v_cache_4740_);
lean_ctor_set(v_reuseFailAlloc_4771_, 6, v_recordedDeps_4741_);
lean_ctor_set(v_reuseFailAlloc_4771_, 7, v_messages_4742_);
lean_ctor_set(v_reuseFailAlloc_4771_, 8, v_infoState_4743_);
lean_ctor_set(v_reuseFailAlloc_4771_, 9, v_snapshotTasks_4744_);
v___x_4766_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4767_ = lean_st_ref_put(v___y_4726_, v___x_4766_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4753_);
v___x_4769_ = v___x_4732_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4753_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_cls_4776_, lean_object* v_msg_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v_cls_4776_, v_msg_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(lean_object* v_o_4784_, lean_object* v_k_4785_, uint8_t v_v_4786_){
_start:
{
lean_object* v_map_4787_; uint8_t v_hasTrace_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4802_; 
v_map_4787_ = lean_ctor_get(v_o_4784_, 0);
v_hasTrace_4788_ = lean_ctor_get_uint8(v_o_4784_, sizeof(void*)*1);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_o_4784_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4790_ = v_o_4784_;
v_isShared_4791_ = v_isSharedCheck_4802_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_map_4787_);
lean_dec(v_o_4784_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4802_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4792_, 0, v_v_4786_);
lean_inc(v_k_4785_);
v___x_4793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4785_, v___x_4792_, v_map_4787_);
if (v_hasTrace_4788_ == 0)
{
lean_object* v___x_4794_; uint8_t v___x_4795_; lean_object* v___x_4797_; 
v___x_4794_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4795_ = l_Lean_Name_isPrefixOf(v___x_4794_, v_k_4785_);
lean_dec(v_k_4785_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4793_);
v___x_4797_ = v___x_4790_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4793_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
lean_ctor_set_uint8(v___x_4797_, sizeof(void*)*1, v___x_4795_);
return v___x_4797_;
}
}
else
{
lean_object* v___x_4800_; 
lean_dec(v_k_4785_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4793_);
v___x_4800_ = v___x_4790_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4793_);
lean_ctor_set_uint8(v_reuseFailAlloc_4801_, sizeof(void*)*1, v_hasTrace_4788_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3___boxed(lean_object* v_o_4803_, lean_object* v_k_4804_, lean_object* v_v_4805_){
_start:
{
uint8_t v_v_boxed_4806_; lean_object* v_res_4807_; 
v_v_boxed_4806_ = lean_unbox(v_v_4805_);
v_res_4807_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(v_o_4803_, v_k_4804_, v_v_boxed_4806_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_opts_4808_, lean_object* v_opt_4809_, uint8_t v_val_4810_){
_start:
{
lean_object* v_name_4811_; lean_object* v___x_4812_; 
v_name_4811_ = lean_ctor_get(v_opt_4809_, 0);
lean_inc(v_name_4811_);
lean_dec_ref(v_opt_4809_);
v___x_4812_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3_spec__3(v_opts_4808_, v_name_4811_, v_val_4810_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_opts_4813_, lean_object* v_opt_4814_, lean_object* v_val_4815_){
_start:
{
uint8_t v_val_boxed_4816_; lean_object* v_res_4817_; 
v_val_boxed_4816_ = lean_unbox(v_val_4815_);
v_res_4817_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(v_opts_4813_, v_opt_4814_, v_val_boxed_4816_);
return v_res_4817_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4821_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4822_ = lean_unsigned_to_nat(18u);
v___x_4823_ = lean_unsigned_to_nat(536u);
v___x_4824_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4825_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4826_ = l_mkPanicMessageWithDecl(v___x_4825_, v___x_4824_, v___x_4823_, v___x_4822_, v___x_4821_);
return v___x_4826_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4828_ = lean_unsigned_to_nat(2u);
v___x_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
lean_ctor_set(v___x_4829_, 1, v___x_4827_);
return v___x_4829_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4830_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4831_ = lean_box(1);
v___x_4832_ = lean_unsigned_to_nat(0u);
v___x_4833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4832_);
lean_ctor_set(v___x_4833_, 1, v___x_4831_);
lean_ctor_set(v___x_4833_, 2, v___x_4830_);
return v___x_4833_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4840_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4841_ = l_Lean_Name_append(v___x_4840_, v___x_4839_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4842_, lean_object* v_optionsPerPos_4843_, lean_object* v_delab_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_fst_4851_; lean_object* v_snd_4852_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4862_; uint8_t v___y_4863_; lean_object* v___y_4883_; lean_object* v___y_4884_; lean_object* v_optionsPerPos_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4915_; lean_object* v_e_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4934_; lean_object* v_e_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v___x_4951_; 
v___x_4951_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4842_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_5102_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_4954_ = v___x_4951_;
v_isShared_4955_ = v_isSharedCheck_5102_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4951_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_5102_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
uint16_t v___y_4957_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v___y_4960_; uint8_t v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; uint8_t v___y_4987_; uint16_t v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; uint8_t v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v___y_5021_; uint8_t v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; lean_object* v_opts_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; uint8_t v___y_5053_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; uint8_t v___y_5064_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v_toCold_5083_; lean_object* v_options_5084_; uint8_t v_hasTrace_5085_; 
v_toCold_5083_ = lean_ctor_get(v_a_4847_, 0);
v_options_5084_ = lean_ctor_get(v_toCold_5083_, 2);
v_hasTrace_5085_ = lean_ctor_get_uint8(v_options_5084_, sizeof(void*)*1);
if (v_hasTrace_5085_ == 0)
{
v___y_5073_ = v_a_4845_;
v___y_5074_ = v_a_4846_;
v___y_5075_ = v_a_4847_;
v___y_5076_ = v_a_4848_;
goto v___jp_5072_;
}
else
{
lean_object* v_inheritedTraceOptions_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; 
v_inheritedTraceOptions_5086_ = lean_ctor_get(v_toCold_5083_, 11);
v___x_5087_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5088_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5086_, v_options_5084_, v___x_5088_);
if (v___x_5089_ == 0)
{
v___y_5073_ = v_a_4845_;
v___y_5074_ = v_a_4846_;
v___y_5075_ = v_a_4847_;
v___y_5076_ = v_a_4848_;
goto v___jp_5072_;
}
else
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5090_ = lean_expr_dbg_to_string(v_a_4952_);
v___x_5091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
v___x_5092_ = l_Lean_MessageData_ofFormat(v___x_5091_);
v___x_5093_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5087_, v___x_5092_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_dec_ref_known(v___x_5093_, 1);
v___y_5073_ = v_a_4845_;
v___y_5074_ = v_a_4846_;
v___y_5075_ = v_a_4847_;
v___y_5076_ = v_a_4848_;
goto v___jp_5072_;
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_del_object(v___x_4954_);
lean_dec(v_a_4952_);
lean_dec_ref(v_delab_4844_);
lean_dec(v_optionsPerPos_4843_);
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5093_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5093_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
}
v___jp_4956_:
{
lean_object* v_toCold_4965_; lean_object* v_currRecDepth_4966_; lean_object* v_ref_4967_; uint8_t v_suppressElabErrors_4968_; uint8_t v_isRecordingDeps_4969_; lean_object* v_fileName_4970_; lean_object* v_fileMap_4971_; lean_object* v_currNamespace_4972_; lean_object* v_openDecls_4973_; lean_object* v_initHeartbeats_4974_; lean_object* v_maxHeartbeats_4975_; lean_object* v_quotContext_4976_; lean_object* v_currMacroScope_4977_; lean_object* v_cancelTk_x3f_4978_; lean_object* v_inheritedTraceOptions_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v_toCold_4965_ = lean_ctor_get(v___y_4963_, 0);
v_currRecDepth_4966_ = lean_ctor_get(v___y_4963_, 1);
v_ref_4967_ = lean_ctor_get(v___y_4963_, 2);
v_suppressElabErrors_4968_ = lean_ctor_get_uint8(v___y_4963_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4969_ = lean_ctor_get_uint8(v___y_4963_, sizeof(void*)*3 + 3);
v_fileName_4970_ = lean_ctor_get(v_toCold_4965_, 0);
v_fileMap_4971_ = lean_ctor_get(v_toCold_4965_, 1);
v_currNamespace_4972_ = lean_ctor_get(v_toCold_4965_, 4);
v_openDecls_4973_ = lean_ctor_get(v_toCold_4965_, 5);
v_initHeartbeats_4974_ = lean_ctor_get(v_toCold_4965_, 6);
v_maxHeartbeats_4975_ = lean_ctor_get(v_toCold_4965_, 7);
v_quotContext_4976_ = lean_ctor_get(v_toCold_4965_, 8);
v_currMacroScope_4977_ = lean_ctor_get(v_toCold_4965_, 9);
v_cancelTk_x3f_4978_ = lean_ctor_get(v_toCold_4965_, 10);
v_inheritedTraceOptions_4979_ = lean_ctor_get(v_toCold_4965_, 11);
v___x_4980_ = l_Lean_maxRecDepth;
v___x_4981_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v___y_4960_, v___x_4980_);
lean_inc_ref(v_inheritedTraceOptions_4979_);
lean_inc(v_cancelTk_x3f_4978_);
lean_inc(v_currMacroScope_4977_);
lean_inc(v_quotContext_4976_);
lean_inc(v_maxHeartbeats_4975_);
lean_inc(v_initHeartbeats_4974_);
lean_inc(v_openDecls_4973_);
lean_inc(v_currNamespace_4972_);
lean_inc_ref(v_fileMap_4971_);
lean_inc_ref(v_fileName_4970_);
v___x_4982_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4982_, 0, v_fileName_4970_);
lean_ctor_set(v___x_4982_, 1, v_fileMap_4971_);
lean_ctor_set(v___x_4982_, 2, v___y_4960_);
lean_ctor_set(v___x_4982_, 3, v___x_4981_);
lean_ctor_set(v___x_4982_, 4, v_currNamespace_4972_);
lean_ctor_set(v___x_4982_, 5, v_openDecls_4973_);
lean_ctor_set(v___x_4982_, 6, v_initHeartbeats_4974_);
lean_ctor_set(v___x_4982_, 7, v_maxHeartbeats_4975_);
lean_ctor_set(v___x_4982_, 8, v_quotContext_4976_);
lean_ctor_set(v___x_4982_, 9, v_currMacroScope_4977_);
lean_ctor_set(v___x_4982_, 10, v_cancelTk_x3f_4978_);
lean_ctor_set(v___x_4982_, 11, v_inheritedTraceOptions_4979_);
lean_inc(v_ref_4967_);
lean_inc(v_currRecDepth_4966_);
v___x_4983_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v_currRecDepth_4966_);
lean_ctor_set(v___x_4983_, 2, v_ref_4967_);
lean_ctor_set_uint16(v___x_4983_, sizeof(void*)*3, v___y_4957_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*3 + 2, v_suppressElabErrors_4968_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*3 + 3, v_isRecordingDeps_4969_);
if (v___y_4961_ == 0)
{
v___y_4934_ = v___y_4958_;
v_e_4935_ = v_a_4952_;
v___y_4936_ = v___y_4959_;
v___y_4937_ = v___y_4962_;
v___y_4938_ = v___x_4983_;
v___y_4939_ = v___y_4964_;
goto v___jp_4933_;
}
else
{
lean_object* v___x_4984_; lean_object* v_a_4985_; 
v___x_4984_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_a_4952_, v___y_4962_);
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref(v___x_4984_);
v___y_4934_ = v___y_4958_;
v_e_4935_ = v_a_4985_;
v___y_4936_ = v___y_4959_;
v___y_4937_ = v___y_4962_;
v___y_4938_ = v___x_4983_;
v___y_4939_ = v___y_4964_;
goto v___jp_4933_;
}
}
v___jp_4986_:
{
lean_object* v___x_4996_; lean_object* v_env_4997_; lean_object* v_nextMacroScope_4998_; lean_object* v_ngen_4999_; lean_object* v_auxDeclNGen_5000_; lean_object* v_traceState_5001_; lean_object* v_recordedDeps_5002_; lean_object* v_messages_5003_; lean_object* v_infoState_5004_; lean_object* v_snapshotTasks_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5015_; 
v___x_4996_ = lean_st_ref_take(v___y_4989_);
v_env_4997_ = lean_ctor_get(v___x_4996_, 0);
v_nextMacroScope_4998_ = lean_ctor_get(v___x_4996_, 1);
v_ngen_4999_ = lean_ctor_get(v___x_4996_, 2);
v_auxDeclNGen_5000_ = lean_ctor_get(v___x_4996_, 3);
v_traceState_5001_ = lean_ctor_get(v___x_4996_, 4);
v_recordedDeps_5002_ = lean_ctor_get(v___x_4996_, 6);
v_messages_5003_ = lean_ctor_get(v___x_4996_, 7);
v_infoState_5004_ = lean_ctor_get(v___x_4996_, 8);
v_snapshotTasks_5005_ = lean_ctor_get(v___x_4996_, 9);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5015_ == 0)
{
lean_object* v_unused_5016_; 
v_unused_5016_ = lean_ctor_get(v___x_4996_, 5);
lean_dec(v_unused_5016_);
v___x_5007_ = v___x_4996_;
v_isShared_5008_ = v_isSharedCheck_5015_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_snapshotTasks_5005_);
lean_inc(v_infoState_5004_);
lean_inc(v_messages_5003_);
lean_inc(v_recordedDeps_5002_);
lean_inc(v_traceState_5001_);
lean_inc(v_auxDeclNGen_5000_);
lean_inc(v_ngen_4999_);
lean_inc(v_nextMacroScope_4998_);
lean_inc(v_env_4997_);
lean_dec(v___x_4996_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5015_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5009_ = l_Lean_Kernel_enableDiag(v_env_4997_, v___y_4987_);
v___x_5010_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1);
if (v_isShared_5008_ == 0)
{
lean_ctor_set(v___x_5007_, 5, v___x_5010_);
lean_ctor_set(v___x_5007_, 0, v___x_5009_);
v___x_5012_ = v___x_5007_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v_nextMacroScope_4998_);
lean_ctor_set(v_reuseFailAlloc_5014_, 2, v_ngen_4999_);
lean_ctor_set(v_reuseFailAlloc_5014_, 3, v_auxDeclNGen_5000_);
lean_ctor_set(v_reuseFailAlloc_5014_, 4, v_traceState_5001_);
lean_ctor_set(v_reuseFailAlloc_5014_, 5, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5014_, 6, v_recordedDeps_5002_);
lean_ctor_set(v_reuseFailAlloc_5014_, 7, v_messages_5003_);
lean_ctor_set(v_reuseFailAlloc_5014_, 8, v_infoState_5004_);
lean_ctor_set(v_reuseFailAlloc_5014_, 9, v_snapshotTasks_5005_);
v___x_5012_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5013_; 
v___x_5013_ = lean_st_ref_put(v___y_4989_, v___x_5012_);
v___y_4957_ = v___y_4988_;
v___y_4958_ = v___y_4992_;
v___y_4959_ = v___y_4991_;
v___y_4960_ = v___y_4993_;
v___y_4961_ = v___y_4994_;
v___y_4962_ = v___y_4995_;
v___y_4963_ = v___y_4990_;
v___y_4964_ = v___y_4989_;
goto v___jp_4956_;
}
}
}
v___jp_5017_:
{
uint16_t v___x_5025_; lean_object* v___x_5026_; lean_object* v_env_5027_; uint8_t v___x_5028_; uint16_t v___x_5029_; uint16_t v___x_5030_; uint16_t v___x_5031_; uint8_t v___x_5032_; 
v___x_5025_ = l_Lean_OptionFlags_ofOptions(v___y_5024_);
v___x_5026_ = lean_st_ref_get(v___y_5018_);
v_env_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc_ref(v_env_5027_);
lean_dec(v___x_5026_);
v___x_5028_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5027_);
lean_dec_ref(v_env_5027_);
v___x_5029_ = 512;
v___x_5030_ = lean_uint16_land(v___x_5025_, v___x_5029_);
v___x_5031_ = 0;
v___x_5032_ = lean_uint16_dec_eq(v___x_5030_, v___x_5031_);
if (v___x_5032_ == 0)
{
if (v___x_5028_ == 0)
{
uint8_t v___x_5033_; 
v___x_5033_ = 1;
v___y_4987_ = v___x_5033_;
v___y_4988_ = v___x_5025_;
v___y_4989_ = v___y_5018_;
v___y_4990_ = v___y_5019_;
v___y_4991_ = v___y_5020_;
v___y_4992_ = v___y_5021_;
v___y_4993_ = v___y_5024_;
v___y_4994_ = v___y_5022_;
v___y_4995_ = v___y_5023_;
goto v___jp_4986_;
}
else
{
v___y_4957_ = v___x_5025_;
v___y_4958_ = v___y_5021_;
v___y_4959_ = v___y_5020_;
v___y_4960_ = v___y_5024_;
v___y_4961_ = v___y_5022_;
v___y_4962_ = v___y_5023_;
v___y_4963_ = v___y_5019_;
v___y_4964_ = v___y_5018_;
goto v___jp_4956_;
}
}
else
{
if (v___x_5028_ == 0)
{
v___y_4957_ = v___x_5025_;
v___y_4958_ = v___y_5021_;
v___y_4959_ = v___y_5020_;
v___y_4960_ = v___y_5024_;
v___y_4961_ = v___y_5022_;
v___y_4962_ = v___y_5023_;
v___y_4963_ = v___y_5019_;
v___y_4964_ = v___y_5018_;
goto v___jp_4956_;
}
else
{
uint8_t v___x_5034_; 
v___x_5034_ = 0;
v___y_4987_ = v___x_5034_;
v___y_4988_ = v___x_5025_;
v___y_4989_ = v___y_5018_;
v___y_4990_ = v___y_5019_;
v___y_4991_ = v___y_5020_;
v___y_4992_ = v___y_5021_;
v___y_4993_ = v___y_5024_;
v___y_4994_ = v___y_5022_;
v___y_4995_ = v___y_5023_;
goto v___jp_4986_;
}
}
}
v___jp_5035_:
{
lean_object* v_toCold_5041_; uint8_t v_isRecordingDeps_5042_; uint8_t v___x_5043_; 
v_toCold_5041_ = lean_ctor_get(v___y_5039_, 0);
v_isRecordingDeps_5042_ = lean_ctor_get_uint8(v___y_5039_, sizeof(void*)*3 + 3);
v___x_5043_ = l_Lean_getPPInstantiateMVars(v_opts_5036_);
if (v_isRecordingDeps_5042_ == 0)
{
lean_inc_ref(v_opts_5036_);
v___y_5018_ = v___y_5040_;
v___y_5019_ = v___y_5039_;
v___y_5020_ = v___y_5037_;
v___y_5021_ = v_opts_5036_;
v___y_5022_ = v___x_5043_;
v___y_5023_ = v___y_5038_;
v___y_5024_ = v_opts_5036_;
goto v___jp_5017_;
}
else
{
lean_object* v_options_5044_; lean_object* v___x_5045_; 
v_options_5044_ = lean_ctor_get(v_toCold_5041_, 2);
lean_inc_ref(v_options_5044_);
v___x_5045_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5044_);
v___y_5018_ = v___y_5040_;
v___y_5019_ = v___y_5039_;
v___y_5020_ = v___y_5037_;
v___y_5021_ = v_opts_5036_;
v___y_5022_ = v___x_5043_;
v___y_5023_ = v___y_5038_;
v___y_5024_ = v___x_5045_;
goto v___jp_5017_;
}
}
v___jp_5046_:
{
if (v___y_5053_ == 0)
{
lean_dec_ref(v___y_5049_);
lean_del_object(v___x_4954_);
v_opts_5036_ = v___y_5052_;
v___y_5037_ = v___y_5051_;
v___y_5038_ = v___y_5050_;
v___y_5039_ = v___y_5047_;
v___y_5040_ = v___y_5048_;
goto v___jp_5035_;
}
else
{
lean_object* v___x_5055_; 
lean_dec_ref(v___y_5052_);
lean_dec(v_a_4952_);
lean_dec_ref(v_delab_4844_);
lean_dec(v_optionsPerPos_4843_);
if (v_isShared_4955_ == 0)
{
lean_ctor_set_tag(v___x_4954_, 1);
lean_ctor_set(v___x_4954_, 0, v___y_5049_);
v___x_5055_ = v___x_4954_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___y_5049_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
v___jp_5057_:
{
if (v___y_5064_ == 0)
{
lean_del_object(v___x_4954_);
v_opts_5036_ = v___y_5063_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5059_;
v___y_5040_ = v___y_5058_;
goto v___jp_5035_;
}
else
{
lean_object* v___x_5065_; 
lean_inc(v_a_4952_);
v___x_5065_ = l_Lean_Meta_isProof(v_a_4952_, v___y_5061_, v___y_5060_, v___y_5059_, v___y_5058_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; 
lean_del_object(v___x_4954_);
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5067_ = lean_unbox(v_a_5066_);
lean_dec(v_a_5066_);
if (v___x_5067_ == 0)
{
v_opts_5036_ = v___y_5063_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5059_;
v___y_5040_ = v___y_5058_;
goto v___jp_5035_;
}
else
{
lean_object* v___x_5068_; 
lean_inc_ref(v___y_5062_);
v___x_5068_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__3(v___y_5063_, v___y_5062_, v___y_5064_);
v_opts_5036_ = v___x_5068_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5059_;
v___y_5040_ = v___y_5058_;
goto v___jp_5035_;
}
}
else
{
lean_object* v_a_5069_; uint8_t v___x_5070_; 
v_a_5069_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5069_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5070_ = l_Lean_Exception_isInterrupt(v_a_5069_);
if (v___x_5070_ == 0)
{
uint8_t v___x_5071_; 
lean_inc(v_a_5069_);
v___x_5071_ = l_Lean_Exception_isRuntime(v_a_5069_);
v___y_5047_ = v___y_5059_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v_a_5069_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
v___y_5052_ = v___y_5063_;
v___y_5053_ = v___x_5071_;
goto v___jp_5046_;
}
else
{
v___y_5047_ = v___y_5059_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v_a_5069_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
v___y_5052_ = v___y_5063_;
v___y_5053_ = v___x_5070_;
goto v___jp_5046_;
}
}
}
}
v___jp_5072_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v___x_5077_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5075_);
v___x_5078_ = l_Lean_pp_proofs;
v___x_5079_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__4(v___x_5077_, v___x_5078_);
v___x_5080_ = lean_box(0);
v___x_5081_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__5(v___x_5079_, v___x_5080_);
lean_dec(v___x_5079_);
if (v___x_5081_ == 0)
{
v___y_5058_ = v___y_5076_;
v___y_5059_ = v___y_5075_;
v___y_5060_ = v___y_5074_;
v___y_5061_ = v___y_5073_;
v___y_5062_ = v___x_5078_;
v___y_5063_ = v___x_5077_;
v___y_5064_ = v___x_5081_;
goto v___jp_5057_;
}
else
{
uint8_t v___x_5082_; 
v___x_5082_ = l_Lean_Expr_isConst(v_a_4952_);
if (v___x_5082_ == 0)
{
v___y_5058_ = v___y_5076_;
v___y_5059_ = v___y_5075_;
v___y_5060_ = v___y_5074_;
v___y_5061_ = v___y_5073_;
v___y_5062_ = v___x_5078_;
v___y_5063_ = v___x_5077_;
v___y_5064_ = v___x_5081_;
goto v___jp_5057_;
}
else
{
lean_del_object(v___x_4954_);
v_opts_5036_ = v___x_5077_;
v___y_5037_ = v___y_5073_;
v___y_5038_ = v___y_5074_;
v___y_5039_ = v___y_5075_;
v___y_5040_ = v___y_5076_;
goto v___jp_5035_;
}
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v_delab_4844_);
lean_dec(v_optionsPerPos_4843_);
v_a_5103_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_4951_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_4951_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
v___jp_4850_:
{
lean_object* v_infos_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_infos_4853_ = lean_ctor_get(v_snd_4852_, 1);
lean_inc(v_infos_4853_);
lean_dec_ref(v_snd_4852_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v_fst_4851_);
lean_ctor_set(v___x_4854_, 1, v_infos_4853_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
return v___x_4855_;
}
v___jp_4856_:
{
if (v___y_4863_ == 0)
{
if (lean_obj_tag(v___y_4862_) == 0)
{
lean_object* v___x_4864_; 
lean_dec_ref(v___y_4858_);
v___x_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___y_4862_);
return v___x_4864_;
}
else
{
lean_object* v_id_4865_; uint8_t v___x_4866_; 
v_id_4865_ = lean_ctor_get(v___y_4862_, 0);
v___x_4866_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4860_, v_id_4865_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; 
lean_dec_ref(v___y_4858_);
v___x_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___y_4862_);
return v___x_4867_;
}
else
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec_ref_known(v___y_4862_, 2);
v___x_4868_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4869_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4868_, v___y_4861_, v___y_4859_, v___y_4858_, v___y_4857_);
lean_dec_ref(v___y_4858_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v_fst_4871_; lean_object* v_snd_4872_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v_fst_4871_ = lean_ctor_get(v_a_4870_, 0);
lean_inc(v_fst_4871_);
v_snd_4872_ = lean_ctor_get(v_a_4870_, 1);
lean_inc(v_snd_4872_);
lean_dec(v_a_4870_);
v_fst_4851_ = v_fst_4871_;
v_snd_4852_ = v_snd_4872_;
goto v___jp_4850_;
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
v_a_4873_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4869_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4869_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
}
}
else
{
lean_object* v___x_4881_; 
lean_dec_ref(v___y_4858_);
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v___y_4862_);
return v___x_4881_;
}
}
v___jp_4882_:
{
lean_object* v_toCold_4890_; lean_object* v_currRecDepth_4891_; uint16_t v_optionFlags_4892_; uint8_t v_suppressElabErrors_4893_; uint8_t v_isRecordingDeps_4894_; lean_object* v_currNamespace_4895_; lean_object* v_openDecls_4896_; lean_object* v_lctx_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; uint8_t v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v_toCold_4890_ = lean_ctor_get(v___y_4888_, 0);
v_currRecDepth_4891_ = lean_ctor_get(v___y_4888_, 1);
v_optionFlags_4892_ = lean_ctor_get_uint16(v___y_4888_, sizeof(void*)*3);
v_suppressElabErrors_4893_ = lean_ctor_get_uint8(v___y_4888_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4894_ = lean_ctor_get_uint8(v___y_4888_, sizeof(void*)*3 + 3);
v_currNamespace_4895_ = lean_ctor_get(v_toCold_4890_, 4);
v_openDecls_4896_ = lean_ctor_get(v_toCold_4890_, 5);
v_lctx_4897_ = lean_ctor_get(v___y_4886_, 2);
v___x_4898_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4899_ = lean_box(0);
v___x_4900_ = l_Lean_Options_getInPattern(v___y_4884_);
lean_dec_ref(v___y_4884_);
v___x_4901_ = l_Lean_SubExpr_mkRoot(v___y_4883_);
v___x_4902_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4897_);
v___x_4903_ = lean_local_ctx_num_indices(v_lctx_4897_);
lean_inc(v_openDecls_4896_);
lean_inc(v_currNamespace_4895_);
v___x_4904_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4904_, 0, v_optionsPerPos_4885_);
lean_ctor_set(v___x_4904_, 1, v_currNamespace_4895_);
lean_ctor_set(v___x_4904_, 2, v_openDecls_4896_);
lean_ctor_set(v___x_4904_, 3, v___x_4901_);
lean_ctor_set(v___x_4904_, 4, v___x_4902_);
lean_ctor_set(v___x_4904_, 5, v___x_4903_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*6, v___x_4900_);
v___x_4905_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4906_ = lean_st_mk_ref(v___x_4905_);
lean_inc(v_currRecDepth_4891_);
lean_inc_ref(v_toCold_4890_);
v___x_4907_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4907_, 0, v_toCold_4890_);
lean_ctor_set(v___x_4907_, 1, v_currRecDepth_4891_);
lean_ctor_set(v___x_4907_, 2, v___x_4899_);
lean_ctor_set_uint16(v___x_4907_, sizeof(void*)*3, v_optionFlags_4892_);
lean_ctor_set_uint8(v___x_4907_, sizeof(void*)*3 + 2, v_suppressElabErrors_4893_);
lean_ctor_set_uint8(v___x_4907_, sizeof(void*)*3 + 3, v_isRecordingDeps_4894_);
lean_inc(v___y_4889_);
lean_inc(v___y_4887_);
lean_inc_ref(v___y_4886_);
lean_inc(v___x_4906_);
v___x_4908_ = lean_apply_7(v_delab_4844_, v___x_4904_, v___x_4906_, v___y_4886_, v___y_4887_, v___x_4907_, v___y_4889_, lean_box(0));
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4910_; 
lean_dec_ref(v___y_4888_);
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
v___x_4910_ = lean_st_ref_get(v___x_4906_);
lean_dec(v___x_4906_);
v_fst_4851_ = v_a_4909_;
v_snd_4852_ = v___x_4910_;
goto v___jp_4850_;
}
else
{
lean_object* v_a_4911_; uint8_t v___x_4912_; 
lean_dec(v___x_4906_);
v_a_4911_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4908_, 1);
v___x_4912_ = l_Lean_Exception_isInterrupt(v_a_4911_);
if (v___x_4912_ == 0)
{
uint8_t v___x_4913_; 
lean_inc(v_a_4911_);
v___x_4913_ = l_Lean_Exception_isRuntime(v_a_4911_);
v___y_4857_ = v___y_4889_;
v___y_4858_ = v___y_4888_;
v___y_4859_ = v___y_4887_;
v___y_4860_ = v___x_4898_;
v___y_4861_ = v___y_4886_;
v___y_4862_ = v_a_4911_;
v___y_4863_ = v___x_4913_;
goto v___jp_4856_;
}
else
{
v___y_4857_ = v___y_4889_;
v___y_4858_ = v___y_4888_;
v___y_4859_ = v___y_4887_;
v___y_4860_ = v___x_4898_;
v___y_4861_ = v___y_4886_;
v___y_4862_ = v_a_4911_;
v___y_4863_ = v___x_4912_;
goto v___jp_4856_;
}
}
}
v___jp_4914_:
{
uint8_t v___x_4921_; 
v___x_4921_ = l_Lean_getPPAll(v___y_4915_);
if (v___x_4921_ == 0)
{
uint8_t v___x_4922_; 
v___x_4922_ = l_Lean_getPPAnalyze(v___y_4915_);
if (v___x_4922_ == 0)
{
v___y_4883_ = v_e_4916_;
v___y_4884_ = v___y_4915_;
v_optionsPerPos_4885_ = v_optionsPerPos_4843_;
v___y_4886_ = v___y_4917_;
v___y_4887_ = v___y_4918_;
v___y_4888_ = v___y_4919_;
v___y_4889_ = v___y_4920_;
goto v___jp_4882_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4843_) == 0)
{
v___y_4883_ = v_e_4916_;
v___y_4884_ = v___y_4915_;
v_optionsPerPos_4885_ = v_optionsPerPos_4843_;
v___y_4886_ = v___y_4917_;
v___y_4887_ = v___y_4918_;
v___y_4888_ = v___y_4919_;
v___y_4889_ = v___y_4920_;
goto v___jp_4882_;
}
else
{
lean_object* v___x_4923_; 
lean_inc_ref(v_e_4916_);
v___x_4923_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
v___y_4883_ = v_e_4916_;
v___y_4884_ = v___y_4915_;
v_optionsPerPos_4885_ = v_a_4924_;
v___y_4886_ = v___y_4917_;
v___y_4887_ = v___y_4918_;
v___y_4888_ = v___y_4919_;
v___y_4889_ = v___y_4920_;
goto v___jp_4882_;
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec_ref(v___y_4919_);
lean_dec_ref(v_e_4916_);
lean_dec_ref(v___y_4915_);
lean_dec_ref(v_delab_4844_);
v_a_4925_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4923_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4923_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
}
}
else
{
v___y_4883_ = v_e_4916_;
v___y_4884_ = v___y_4915_;
v_optionsPerPos_4885_ = v_optionsPerPos_4843_;
v___y_4886_ = v___y_4917_;
v___y_4887_ = v___y_4918_;
v___y_4888_ = v___y_4919_;
v___y_4889_ = v___y_4920_;
goto v___jp_4882_;
}
}
v___jp_4933_:
{
uint8_t v___x_4940_; 
v___x_4940_ = l_Lean_getPPBeta(v___y_4934_);
if (v___x_4940_ == 0)
{
v___y_4915_ = v___y_4934_;
v_e_4916_ = v_e_4935_;
v___y_4917_ = v___y_4936_;
v___y_4918_ = v___y_4937_;
v___y_4919_ = v___y_4938_;
v___y_4920_ = v___y_4939_;
goto v___jp_4914_;
}
else
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_Core_betaReduce(v_e_4935_, v___y_4938_, v___y_4939_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
lean_inc(v_a_4942_);
lean_dec_ref_known(v___x_4941_, 1);
v___y_4915_ = v___y_4934_;
v_e_4916_ = v_a_4942_;
v___y_4917_ = v___y_4936_;
v___y_4918_ = v___y_4937_;
v___y_4919_ = v___y_4938_;
v___y_4920_ = v___y_4939_;
goto v___jp_4914_;
}
else
{
lean_object* v_a_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4950_; 
lean_dec_ref(v___y_4938_);
lean_dec_ref(v___y_4934_);
lean_dec_ref(v_delab_4844_);
lean_dec(v_optionsPerPos_4843_);
v_a_4943_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4941_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4941_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4948_; 
if (v_isShared_4946_ == 0)
{
v___x_4948_ = v___x_4945_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5111_, lean_object* v_optionsPerPos_5112_, lean_object* v_delab_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5111_, v_optionsPerPos_5112_, v_delab_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5120_, lean_object* v_e_5121_, lean_object* v_optionsPerPos_5122_, lean_object* v_delab_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5121_, v_optionsPerPos_5122_, v_delab_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5130_, lean_object* v_e_5131_, lean_object* v_optionsPerPos_5132_, lean_object* v_delab_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5130_, v_e_5131_, v_optionsPerPos_5132_, v_delab_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5141_, lean_object* v_optionsPerPos_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5149_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5141_, v_optionsPerPos_5142_, v___x_5148_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5158_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5158_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5158_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v_fst_5154_; lean_object* v___x_5156_; 
v_fst_5154_ = lean_ctor_get(v_a_5150_, 0);
lean_inc(v_fst_5154_);
lean_dec(v_a_5150_);
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 0, v_fst_5154_);
v___x_5156_ = v___x_5152_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_fst_5154_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
v_a_5159_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5149_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5149_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5167_, lean_object* v_optionsPerPos_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_PrettyPrinter_delab(v_e_5167_, v_optionsPerPos_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_);
lean_dec(v_a_5172_);
lean_dec_ref(v_a_5171_);
lean_dec(v_a_5170_);
lean_dec_ref(v_a_5169_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5239_; uint8_t v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5239_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5240_ = 0;
v___x_5241_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5242_ = l_Lean_registerTraceClass(v___x_5239_, v___x_5240_, v___x_5241_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
lean_dec_ref_known(v___x_5242_, 1);
v___x_5243_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5244_ = l_Lean_registerTraceClass(v___x_5243_, v___x_5240_, v___x_5241_);
return v___x_5244_;
}
else
{
return v___x_5242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5246_;
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
