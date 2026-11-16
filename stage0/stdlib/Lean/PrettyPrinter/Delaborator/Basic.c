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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
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
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "builtin_delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 78, 157, 22, 7, 109, 94, 150)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 48, 28, 192, 106, 44, 69, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Register a delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 145, 52, 44, 66, 160, 163, 69)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "delabAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 105, 4, 51, 2, 59, 203, 237)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 512, .m_capacity = 512, .m_length = 511, .m_data = "Registers a delaborator.\n\n`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the\n`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`, elaborators\nfor `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\") to reduce\nspecial casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(102) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(133) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value),LEAN_SCALAR_PTR_LITERAL(231, 152, 1, 212, 81, 225, 23, 202)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__17 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__18 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Register an unexpander for applications of a given constant."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unexpander"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "appUnexpanderAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 177, 70, 181, 38, 19, 76, 236)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 619, .m_capacity = 619, .m_length = 618, .m_data = "Registers an unexpander for applications of a given constant.\n\n`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant\n`c`. The unexpander is passed the result of pre-pretty printing the application *without*\nimplicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,\nit will not be called at all.\n\nUnexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without\nspecial imports. This however also makes them much less capable since they can only transform\nsyntax and don't have access to the expression tree."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(499) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(488) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(488) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 19, 214, 208, 28, 243, 5, 52)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 164, 190, 165, 103, 227, 105, 51)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 183, 224, 255, 20, 2, 99, 61)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 0, 36, 13, 230, 137, 208, 68)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 99, 145, 72, 150, 13, 224, 205)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 207, 248, 169, 211, 175, 254, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 170, 24, 58, 43, 56, 104, 232)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 123, 18, 109, 183, 228, 66, 1)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 193, 243, 64, 48, 31, 65, 146)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 168, 97, 241, 156, 42, 72, 1)}};
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(uint8_t v_builtin_359_, lean_object* v_declName_360_, lean_object* v_key_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object* v_builtin_367_, lean_object* v_declName_368_, lean_object* v_key_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_builtin_boxed_373_; lean_object* v_res_374_; 
v_builtin_boxed_373_ = lean_unbox(v_builtin_367_);
v_res_374_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(v_builtin_boxed_373_, v_declName_368_, v_key_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v_key_369_);
lean_dec(v_declName_368_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_375_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
lean_ctor_set(v___x_380_, 3, v___x_379_);
lean_ctor_set(v___x_380_, 4, v___x_378_);
lean_ctor_set(v___x_380_, 5, v___x_378_);
lean_ctor_set(v___x_380_, 6, v___x_378_);
lean_ctor_set(v___x_380_, 7, v___x_378_);
lean_ctor_set(v___x_380_, 8, v___x_378_);
lean_ctor_set(v___x_380_, 9, v___x_378_);
lean_ctor_set(v___x_380_, 10, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(32u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4(void){
_start:
{
size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_384_ = ((size_t)5ULL);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_unsigned_to_nat(32u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__3);
v___x_389_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_385_);
lean_ctor_set(v___x_389_, 3, v___x_385_);
lean_ctor_set_usize(v___x_389_, 4, v___x_384_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = lean_box(1);
v___x_391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4);
v___x_392_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__1);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v_toCold_399_; lean_object* v_env_400_; lean_object* v_options_401_; uint8_t v___x_402_; lean_object* v_env_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_398_ = lean_st_ref_get(v___y_396_);
v_toCold_399_ = lean_ctor_get(v___y_395_, 0);
v_env_400_ = lean_ctor_get(v___x_398_, 0);
lean_inc_ref(v_env_400_);
lean_dec(v___x_398_);
v_options_401_ = lean_ctor_get(v_toCold_399_, 2);
v___x_402_ = 0;
v_env_403_ = l_Lean_Environment_setRecordingDeps(v_env_400_, v___x_402_);
v___x_404_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2);
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5);
lean_inc_ref(v_options_401_);
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v_env_403_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
lean_ctor_set(v___x_406_, 3, v_options_401_);
v___x_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_msgData_394_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msgData_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_ref_418_; lean_object* v___x_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_ref_418_ = lean_ctor_get(v___y_415_, 2);
v___x_419_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_414_, v___y_415_, v___y_416_);
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_ref_418_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_ref_418_);
lean_ctor_set(v___x_424_, 1, v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_toCold_439_; lean_object* v_currRecDepth_440_; lean_object* v_ref_441_; uint16_t v_optionFlags_442_; uint8_t v_suppressElabErrors_443_; uint8_t v_checkDeprecated_444_; uint8_t v_isRecordingDeps_445_; lean_object* v_ref_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_toCold_439_ = lean_ctor_get(v___y_436_, 0);
v_currRecDepth_440_ = lean_ctor_get(v___y_436_, 1);
v_ref_441_ = lean_ctor_get(v___y_436_, 2);
v_optionFlags_442_ = lean_ctor_get_uint16(v___y_436_, sizeof(void*)*3);
v_suppressElabErrors_443_ = lean_ctor_get_uint8(v___y_436_, sizeof(void*)*3 + 2);
v_checkDeprecated_444_ = lean_ctor_get_uint8(v___y_436_, sizeof(void*)*3 + 3);
v_isRecordingDeps_445_ = lean_ctor_get_uint8(v___y_436_, sizeof(void*)*3 + 4);
v_ref_446_ = l_Lean_replaceRef(v_ref_434_, v_ref_441_);
lean_inc(v_currRecDepth_440_);
lean_inc_ref(v_toCold_439_);
v___x_447_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_447_, 0, v_toCold_439_);
lean_ctor_set(v___x_447_, 1, v_currRecDepth_440_);
lean_ctor_set(v___x_447_, 2, v_ref_446_);
lean_ctor_set_uint16(v___x_447_, sizeof(void*)*3, v_optionFlags_442_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 2, v_suppressElabErrors_443_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 3, v_checkDeprecated_444_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 4, v_isRecordingDeps_445_);
v___x_448_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_435_, v___x_447_, v___y_437_);
lean_dec_ref_known(v___x_447_, 3);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_449_, v_msg_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v_ref_449_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_476_, lean_object* v_declHint_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_env_482_; uint8_t v___x_483_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_st_ref_get(v___y_478_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_env_482_);
lean_dec(v___x_481_);
v___x_483_ = l_Lean_Name_isAnonymous(v_declHint_477_);
if (v___x_483_ == 0)
{
uint8_t v_isExporting_484_; 
v_isExporting_484_ = lean_ctor_get_uint8(v_env_482_, sizeof(void*)*13);
if (v_isExporting_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec_ref(v_env_482_);
lean_dec(v_declHint_477_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_msg_476_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; uint8_t v___x_487_; 
lean_inc_ref(v_env_482_);
v___x_486_ = l_Lean_Environment_setExporting(v_env_482_, v___x_483_);
lean_inc(v_declHint_477_);
lean_inc_ref(v___x_486_);
v___x_487_ = l_Lean_Environment_contains(v___x_486_, v_declHint_477_, v_isExporting_484_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v___x_486_);
lean_dec_ref(v_env_482_);
lean_dec(v_declHint_477_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_msg_476_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_c_494_; lean_object* v___x_495_; 
v___x_489_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__2);
v___x_490_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__5);
v___x_491_ = l_Lean_Options_empty;
lean_inc_ref(v___x_486_);
v___x_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_492_, 0, v___x_486_);
lean_ctor_set(v___x_492_, 1, v___x_489_);
lean_ctor_set(v___x_492_, 2, v___x_490_);
lean_ctor_set(v___x_492_, 3, v___x_491_);
lean_inc(v_declHint_477_);
v___x_493_ = l_Lean_MessageData_ofConstName(v_declHint_477_, v___x_483_);
v_c_494_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_494_, 0, v___x_492_);
lean_ctor_set(v_c_494_, 1, v___x_493_);
v___x_495_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_486_, v_declHint_477_);
lean_dec_ref(v___x_486_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v_env_482_);
lean_dec(v_declHint_477_);
v___x_496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_c_494_);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_MessageData_note(v___x_499_);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v_msg_476_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_537_; 
v_val_503_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_537_ == 0)
{
v___x_505_ = v___x_495_;
v_isShared_506_ = v_isSharedCheck_537_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_495_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_537_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v_moduleNames_508_; lean_object* v_mod_509_; uint8_t v___x_510_; 
v___x_507_ = l_Lean_Environment_header(v_env_482_);
lean_dec_ref(v_env_482_);
v_moduleNames_508_ = lean_ctor_get(v___x_507_, 4);
lean_inc_ref(v_moduleNames_508_);
lean_dec_ref(v___x_507_);
v_mod_509_ = lean_array_get(v___x_480_, v_moduleNames_508_, v_val_503_);
lean_dec(v_val_503_);
lean_dec_ref(v_moduleNames_508_);
v___x_510_ = l_Lean_isPrivateName(v_declHint_477_);
lean_dec(v_declHint_477_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_c_494_);
v___x_513_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l_Lean_MessageData_ofName(v_mod_509_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_MessageData_note(v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v_msg_476_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 0, v___x_520_);
v___x_522_ = v___x_505_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_c_494_);
v___x_526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_MessageData_ofName(v_mod_509_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_MessageData_note(v___x_531_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v_msg_476_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 0, v___x_533_);
v___x_535_ = v___x_505_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_538_; 
lean_dec_ref(v_env_482_);
lean_dec(v_declHint_477_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_msg_476_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_539_, lean_object* v_declHint_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_539_, v_declHint_540_, v___y_541_);
lean_dec(v___y_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object* v_msg_544_, lean_object* v_declHint_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_559_; 
v___x_549_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_544_, v_declHint_545_, v___y_547_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = l_Lean_unknownIdentifierMessageTag;
v___x_555_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_a_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_560_, lean_object* v_declHint_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_560_, v_declHint_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_566_, lean_object* v_msg_567_, lean_object* v_declHint_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_567_, v_declHint_568_, v___y_569_, v___y_570_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
v___x_574_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_566_, v_a_573_, v___y_569_, v___y_570_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_575_, lean_object* v_msg_576_, lean_object* v_declHint_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_575_, v_msg_576_, v_declHint_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v_ref_575_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object* v_ref_588_, lean_object* v_constName_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_593_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1);
v___x_594_ = 0;
lean_inc(v_constName_589_);
v___x_595_ = l_Lean_MessageData_ofConstName(v_constName_589_, v___x_594_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_593_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_588_, v___x_598_, v_constName_589_, v___y_590_, v___y_591_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_ref_600_, lean_object* v_constName_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_600_, v_constName_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v_ref_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object* v_constName_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_ref_610_; lean_object* v___x_611_; 
v_ref_610_ = lean_ctor_get(v___y_607_, 2);
v___x_611_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_610_, v_constName_606_, v___y_607_, v___y_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_constName_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_constName_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v_env_622_; uint8_t v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_st_ref_get(v___y_619_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_621_);
v___x_623_ = 0;
lean_inc(v_constName_617_);
v___x_624_ = l_Lean_Environment_findConstVal_x3f(v_env_622_, v_constName_617_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_617_, v___y_618_, v___y_619_);
return v___x_625_;
}
else
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_constName_617_);
v_val_626_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_val_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_constName_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
if (lean_obj_tag(v_a_639_) == 0)
{
lean_object* v___x_641_; 
v___x_641_ = l_List_reverse___redArg(v_a_640_);
return v___x_641_;
}
else
{
lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
v_head_642_ = lean_ctor_get(v_a_639_, 0);
v_tail_643_ = lean_ctor_get(v_a_639_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_645_ = v_a_639_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_tail_643_);
lean_inc(v_head_642_);
lean_dec(v_a_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_mkLevelParam(v_head_642_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v_a_640_);
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_640_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v_a_639_ = v_tail_643_;
v_a_640_ = v___x_649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_constName_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
lean_inc(v_constName_653_);
v___x_657_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_669_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_669_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_levelParams_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_levelParams_662_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_levelParams_662_);
lean_dec(v_a_658_);
v___x_663_ = lean_box(0);
v___x_664_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_levelParams_662_, v___x_663_);
v___x_665_ = l_Lean_mkConst(v_constName_653_, v___x_664_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_665_);
v___x_667_ = v___x_660_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_constName_653_);
v_a_670_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_657_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_657_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_constName_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6(v_constName_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_t_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; lean_object* v_infoState_687_; uint8_t v_enabled_688_; 
v___x_686_ = lean_st_ref_get(v___y_684_);
v_infoState_687_ = lean_ctor_get(v___x_686_, 8);
lean_inc_ref(v_infoState_687_);
lean_dec(v___x_686_);
v_enabled_688_ = lean_ctor_get_uint8(v_infoState_687_, sizeof(void*)*3);
lean_dec_ref(v_infoState_687_);
if (v_enabled_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_t_683_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v_infoState_692_; lean_object* v_env_693_; lean_object* v_nextMacroScope_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_traceState_697_; lean_object* v_cache_698_; lean_object* v_recordedDeps_699_; lean_object* v_messages_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_723_; 
v___x_691_ = lean_st_ref_take(v___y_684_);
v_infoState_692_ = lean_ctor_get(v___x_691_, 8);
v_env_693_ = lean_ctor_get(v___x_691_, 0);
v_nextMacroScope_694_ = lean_ctor_get(v___x_691_, 1);
v_ngen_695_ = lean_ctor_get(v___x_691_, 2);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_691_, 3);
v_traceState_697_ = lean_ctor_get(v___x_691_, 4);
v_cache_698_ = lean_ctor_get(v___x_691_, 5);
v_recordedDeps_699_ = lean_ctor_get(v___x_691_, 6);
v_messages_700_ = lean_ctor_get(v___x_691_, 7);
v_snapshotTasks_701_ = lean_ctor_get(v___x_691_, 9);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_723_ == 0)
{
v___x_703_ = v___x_691_;
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_692_);
lean_inc(v_messages_700_);
lean_inc(v_recordedDeps_699_);
lean_inc(v_cache_698_);
lean_inc(v_traceState_697_);
lean_inc(v_auxDeclNGen_696_);
lean_inc(v_ngen_695_);
lean_inc(v_nextMacroScope_694_);
lean_inc(v_env_693_);
lean_dec(v___x_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v_enabled_705_; lean_object* v_assignment_706_; lean_object* v_lazyAssignment_707_; lean_object* v_trees_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_722_; 
v_enabled_705_ = lean_ctor_get_uint8(v_infoState_692_, sizeof(void*)*3);
v_assignment_706_ = lean_ctor_get(v_infoState_692_, 0);
v_lazyAssignment_707_ = lean_ctor_get(v_infoState_692_, 1);
v_trees_708_ = lean_ctor_get(v_infoState_692_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_infoState_692_);
if (v_isSharedCheck_722_ == 0)
{
v___x_710_ = v_infoState_692_;
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_trees_708_);
lean_inc(v_lazyAssignment_707_);
lean_inc(v_assignment_706_);
lean_dec(v_infoState_692_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_722_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = lean_box(0);
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_trees_708_, v_t_683_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 2, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_assignment_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_lazyAssignment_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_721_, sizeof(void*)*3, v_enabled_705_);
v___x_715_ = v_reuseFailAlloc_721_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 8, v___x_715_);
v___x_717_ = v___x_703_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_env_693_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_nextMacroScope_694_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_ngen_695_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_auxDeclNGen_696_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_traceState_697_);
lean_ctor_set(v_reuseFailAlloc_720_, 5, v_cache_698_);
lean_ctor_set(v_reuseFailAlloc_720_, 6, v_recordedDeps_699_);
lean_ctor_set(v_reuseFailAlloc_720_, 7, v_messages_700_);
lean_ctor_set(v_reuseFailAlloc_720_, 8, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_720_, 9, v_snapshotTasks_701_);
v___x_717_ = v_reuseFailAlloc_720_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_st_ref_put(v___y_684_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_712_);
return v___x_719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_724_, v___y_725_);
lean_dec(v___y_725_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(32u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
size_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_731_ = ((size_t)5ULL);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_unsigned_to_nat(32u);
v___x_734_ = lean_mk_empty_array_with_capacity(v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_736_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_732_);
lean_ctor_set(v___x_736_, 3, v___x_732_);
lean_ctor_set_usize(v___x_736_, 4, v___x_731_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v_infoState_742_; uint8_t v_enabled_743_; 
v___x_741_ = lean_st_ref_get(v___y_739_);
v_infoState_742_ = lean_ctor_get(v___x_741_, 8);
lean_inc_ref(v_infoState_742_);
lean_dec(v___x_741_);
v_enabled_743_ = lean_ctor_get_uint8(v_infoState_742_, sizeof(void*)*3);
lean_dec_ref(v_infoState_742_);
if (v_enabled_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref(v_t_737_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v_t_737_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_747_, v___y_739_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_t_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0(v_t_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2(lean_object* v_stx_754_, lean_object* v_n_755_, lean_object* v_expectedType_x3f_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6(v_n_755_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_stx_754_);
v___x_764_ = l_Lean_LocalContext_empty;
v___x_765_ = 0;
v___x_766_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_766_, 0, v___x_763_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v_expectedType_x3f_756_);
lean_ctor_set(v___x_766_, 3, v_a_761_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*4, v___x_765_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*4 + 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0(v___x_767_, v___y_757_, v___y_758_);
return v___x_768_;
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_expectedType_x3f_756_);
lean_dec(v_stx_754_);
v_a_769_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_760_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_760_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_777_, lean_object* v_n_778_, lean_object* v_expectedType_x3f_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2(v_stx_777_, v_n_778_, v_expectedType_x3f_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0(lean_object* v_info_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_788_, 0, v_info_784_);
v___x_789_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0(v___x_788_, v___y_785_, v___y_786_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0___boxed(lean_object* v_info_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0(v_info_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(0);
return v___x_797_;
}
else
{
lean_object* v_key_798_; lean_object* v_value_799_; lean_object* v_tail_800_; uint8_t v___x_801_; 
v_key_798_ = lean_ctor_get(v_x_796_, 0);
v_value_799_ = lean_ctor_get(v_x_796_, 1);
v_tail_800_ = lean_ctor_get(v_x_796_, 2);
v___x_801_ = lean_name_eq(v_key_798_, v_a_795_);
if (v___x_801_ == 0)
{
v_x_796_ = v_tail_800_;
goto _start;
}
else
{
lean_object* v___x_803_; 
lean_inc(v_value_799_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_value_799_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec(v_a_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_m_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_buckets_809_; lean_object* v___x_810_; uint64_t v___y_812_; 
v_buckets_809_ = lean_ctor_get(v_m_807_, 1);
v___x_810_ = lean_array_get_size(v_buckets_809_);
if (lean_obj_tag(v_a_808_) == 0)
{
uint64_t v___x_826_; 
v___x_826_ = 1723ULL;
v___y_812_ = v___x_826_;
goto v___jp_811_;
}
else
{
uint64_t v_hash_827_; 
v_hash_827_ = lean_ctor_get_uint64(v_a_808_, sizeof(void*)*2);
v___y_812_ = v_hash_827_;
goto v___jp_811_;
}
v___jp_811_:
{
uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v_fold_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_813_ = 32ULL;
v___x_814_ = lean_uint64_shift_right(v___y_812_, v___x_813_);
v_fold_815_ = lean_uint64_xor(v___y_812_, v___x_814_);
v___x_816_ = 16ULL;
v___x_817_ = lean_uint64_shift_right(v_fold_815_, v___x_816_);
v___x_818_ = lean_uint64_xor(v_fold_815_, v___x_817_);
v___x_819_ = lean_uint64_to_usize(v___x_818_);
v___x_820_ = lean_usize_of_nat(v___x_810_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_sub(v___x_820_, v___x_821_);
v___x_823_ = lean_usize_land(v___x_819_, v___x_822_);
v___x_824_ = lean_array_uget_borrowed(v_buckets_809_, v___x_823_);
v___x_825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_808_, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_m_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_m_828_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_keys_831_, lean_object* v_i_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_array_get_size(v_keys_831_);
v___x_835_ = lean_nat_dec_lt(v_i_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_i_832_);
return v___x_835_;
}
else
{
lean_object* v_k_x27_836_; uint8_t v___x_837_; 
v_k_x27_836_ = lean_array_fget_borrowed(v_keys_831_, v_i_832_);
v___x_837_ = l_Lean_instBEqExtraModUse_beq(v_k_833_, v_k_x27_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_i_832_, v___x_838_);
lean_dec(v_i_832_);
v_i_832_ = v___x_839_;
goto _start;
}
else
{
lean_dec(v_i_832_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_keys_841_, lean_object* v_i_842_, lean_object* v_k_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_841_, v_i_842_, v_k_843_);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_keys_841_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_846_, size_t v_x_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v_es_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v_j_853_; lean_object* v___x_854_; 
v_es_849_ = lean_ctor_get(v_x_846_, 0);
v___x_850_ = lean_box(2);
v___x_851_ = ((size_t)31ULL);
v___x_852_ = lean_usize_land(v_x_847_, v___x_851_);
v_j_853_ = lean_usize_to_nat(v___x_852_);
v___x_854_ = lean_array_get_borrowed(v___x_850_, v_es_849_, v_j_853_);
lean_dec(v_j_853_);
switch(lean_obj_tag(v___x_854_))
{
case 0:
{
lean_object* v_key_855_; uint8_t v___x_856_; 
v_key_855_ = lean_ctor_get(v___x_854_, 0);
v___x_856_ = l_Lean_instBEqExtraModUse_beq(v_x_848_, v_key_855_);
return v___x_856_;
}
case 1:
{
lean_object* v_node_857_; size_t v___x_858_; size_t v___x_859_; 
v_node_857_ = lean_ctor_get(v___x_854_, 0);
v___x_858_ = ((size_t)5ULL);
v___x_859_ = lean_usize_shift_right(v_x_847_, v___x_858_);
v_x_846_ = v_node_857_;
v_x_847_ = v___x_859_;
goto _start;
}
default: 
{
uint8_t v___x_861_; 
v___x_861_ = 0;
return v___x_861_;
}
}
}
else
{
lean_object* v_ks_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_ks_862_ = lean_ctor_get(v_x_846_, 0);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_ks_862_, v___x_863_, v_x_848_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
size_t v_x_8555__boxed_868_; uint8_t v_res_869_; lean_object* v_r_870_; 
v_x_8555__boxed_868_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_869_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_865_, v_x_8555__boxed_868_, v_x_867_);
lean_dec_ref(v_x_867_);
lean_dec_ref(v_x_865_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint64_t v___x_873_; size_t v___x_874_; uint8_t v___x_875_; 
v___x_873_ = l_Lean_instHashableExtraModUse_hash(v_x_872_);
v___x_874_ = lean_uint64_to_usize(v___x_873_);
v___x_875_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_871_, v___x_874_, v_x_872_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_876_, v_x_877_);
lean_dec_ref(v_x_877_);
lean_dec_ref(v_x_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___lam__0(lean_object* v___x_880_, lean_object* v_entry_881_, lean_object* v_s_882_){
_start:
{
lean_object* v_addEntryFn_883_; lean_object* v_importedEntries_884_; lean_object* v_state_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_addEntryFn_883_ = lean_ctor_get(v___x_880_, 3);
lean_inc(v_addEntryFn_883_);
lean_dec_ref(v___x_880_);
v_importedEntries_884_ = lean_ctor_get(v_s_882_, 0);
v_state_885_ = lean_ctor_get(v_s_882_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_s_882_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_s_882_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_state_885_);
lean_inc(v_importedEntries_884_);
lean_dec(v_s_882_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_state_889_; lean_object* v___x_891_; 
v_state_889_ = lean_apply_2(v_addEntryFn_883_, v_state_885_, v_entry_881_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_state_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_importedEntries_884_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_state_889_);
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
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_894_; double v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_float_of_nat(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_cls_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_ref_904_; lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_951_; 
v_ref_904_ = lean_ctor_get(v___y_901_, 2);
v___x_905_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_900_, v___y_901_, v___y_902_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_951_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_951_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_951_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v_traceState_911_; lean_object* v_env_912_; lean_object* v_nextMacroScope_913_; lean_object* v_ngen_914_; lean_object* v_auxDeclNGen_915_; lean_object* v_cache_916_; lean_object* v_recordedDeps_917_; lean_object* v_messages_918_; lean_object* v_infoState_919_; lean_object* v_snapshotTasks_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_950_; 
v___x_910_ = lean_st_ref_take(v___y_902_);
v_traceState_911_ = lean_ctor_get(v___x_910_, 4);
v_env_912_ = lean_ctor_get(v___x_910_, 0);
v_nextMacroScope_913_ = lean_ctor_get(v___x_910_, 1);
v_ngen_914_ = lean_ctor_get(v___x_910_, 2);
v_auxDeclNGen_915_ = lean_ctor_get(v___x_910_, 3);
v_cache_916_ = lean_ctor_get(v___x_910_, 5);
v_recordedDeps_917_ = lean_ctor_get(v___x_910_, 6);
v_messages_918_ = lean_ctor_get(v___x_910_, 7);
v_infoState_919_ = lean_ctor_get(v___x_910_, 8);
v_snapshotTasks_920_ = lean_ctor_get(v___x_910_, 9);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_950_ == 0)
{
v___x_922_ = v___x_910_;
v_isShared_923_ = v_isSharedCheck_950_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snapshotTasks_920_);
lean_inc(v_infoState_919_);
lean_inc(v_messages_918_);
lean_inc(v_recordedDeps_917_);
lean_inc(v_cache_916_);
lean_inc(v_traceState_911_);
lean_inc(v_auxDeclNGen_915_);
lean_inc(v_ngen_914_);
lean_inc(v_nextMacroScope_913_);
lean_inc(v_env_912_);
lean_dec(v___x_910_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_950_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint64_t v_tid_924_; lean_object* v_traces_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_949_; 
v_tid_924_ = lean_ctor_get_uint64(v_traceState_911_, sizeof(void*)*1);
v_traces_925_ = lean_ctor_get(v_traceState_911_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_traceState_911_);
if (v_isSharedCheck_949_ == 0)
{
v___x_927_ = v_traceState_911_;
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_traces_925_);
lean_dec(v_traceState_911_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; double v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_929_ = lean_box(0);
v___x_930_ = lean_box(0);
v___x_931_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_932_ = 0;
v___x_933_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_934_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_934_, 0, v_cls_899_);
lean_ctor_set(v___x_934_, 1, v___x_930_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
lean_ctor_set_float(v___x_934_, sizeof(void*)*3, v___x_931_);
lean_ctor_set_float(v___x_934_, sizeof(void*)*3 + 8, v___x_931_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 16, v___x_932_);
v___x_935_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_936_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v_a_906_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_inc(v_ref_904_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_ref_904_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_PersistentArray_push___redArg(v_traces_925_, v___x_937_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_938_);
v___x_940_ = v___x_927_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set_uint64(v_reuseFailAlloc_948_, sizeof(void*)*1, v_tid_924_);
v___x_940_ = v_reuseFailAlloc_948_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 4, v___x_940_);
v___x_942_ = v___x_922_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_env_912_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_nextMacroScope_913_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_ngen_914_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_auxDeclNGen_915_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_cache_916_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_recordedDeps_917_);
lean_ctor_set(v_reuseFailAlloc_947_, 7, v_messages_918_);
lean_ctor_set(v_reuseFailAlloc_947_, 8, v_infoState_919_);
lean_ctor_set(v_reuseFailAlloc_947_, 9, v_snapshotTasks_920_);
v___x_942_ = v_reuseFailAlloc_947_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_st_ref_put(v___y_902_, v___x_942_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_929_);
v___x_945_ = v___x_908_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_929_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_cls_952_, lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_952_, v_msg_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_957_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__0);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_962_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__5));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v_cls_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_cls_977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_978_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_979_ = l_Lean_Name_append(v___x_978_, v_cls_977_);
return v___x_979_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__13));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__15));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_mod_990_, uint8_t v_isMeta_991_, lean_object* v_hint_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_env_1014_; uint8_t v_isExporting_1015_; lean_object* v_entry_1016_; lean_object* v___x_1017_; lean_object* v_env_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_1013_ = lean_st_ref_get(v___y_994_);
v_env_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_env_1014_);
lean_dec(v___x_1013_);
v_isExporting_1015_ = lean_ctor_get_uint8(v_env_1014_, sizeof(void*)*13);
lean_dec_ref(v_env_1014_);
lean_inc(v_mod_990_);
v_entry_1016_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1016_, 0, v_mod_990_);
lean_ctor_set_uint8(v_entry_1016_, sizeof(void*)*1, v_isExporting_1015_);
lean_ctor_set_uint8(v_entry_1016_, sizeof(void*)*1 + 1, v_isMeta_991_);
v___x_1017_ = lean_st_ref_get(v___y_994_);
v_env_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_env_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1020_ = lean_box(1);
v___x_1021_ = lean_box(0);
v___x_1022_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1012_, v___x_1019_, v_env_1018_, v___x_1020_, v___x_1021_);
v___x_1023_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v___x_1022_, v_entry_1016_);
lean_dec(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v_toCold_1024_; lean_object* v_options_1025_; lean_object* v_inheritedTraceOptions_1026_; uint8_t v_hasTrace_1027_; lean_object* v___f_1028_; uint8_t v___x_1029_; lean_object* v___y_1031_; 
v_toCold_1024_ = lean_ctor_get(v___y_993_, 0);
v_options_1025_ = lean_ctor_get(v_toCold_1024_, 2);
v_inheritedTraceOptions_1026_ = lean_ctor_get(v_toCold_1024_, 11);
v_hasTrace_1027_ = lean_ctor_get_uint8(v_options_1025_, sizeof(void*)*1);
v___f_1028_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_1028_, 0, v___x_1019_);
lean_closure_set(v___f_1028_, 1, v_entry_1016_);
v___x_1029_ = 1;
if (v_hasTrace_1027_ == 0)
{
lean_dec(v_hint_992_);
lean_dec(v_mod_990_);
v___y_1031_ = v___y_994_;
goto v___jp_1030_;
}
else
{
lean_object* v_cls_1049_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_cls_1049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__4));
v___x_1069_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__12);
v___x_1070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1026_, v_options_1025_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_hint_992_);
lean_dec(v_mod_990_);
v___y_1031_ = v___y_994_;
goto v___jp_1030_;
}
else
{
lean_object* v___x_1071_; lean_object* v___y_1073_; 
v___x_1071_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__14);
if (v_isExporting_1015_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__19));
v___y_1073_ = v___x_1080_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__20));
v___y_1073_ = v___x_1081_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_inc_ref(v___y_1073_);
v___x_1074_ = l_Lean_stringToMessageData(v___y_1073_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1071_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__16);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
if (v_isMeta_991_ == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__17));
v___y_1056_ = v___x_1077_;
v___y_1057_ = v___x_1078_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__18));
v___y_1056_ = v___x_1077_;
v___y_1057_ = v___x_1079_;
goto v___jp_1055_;
}
}
}
v___jp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1051_);
lean_ctor_set(v___x_1053_, 1, v___y_1052_);
v___x_1054_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_1049_, v___x_1053_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_dec_ref_known(v___x_1054_, 1);
v___y_1031_ = v___y_994_;
goto v___jp_1030_;
}
else
{
lean_dec_ref(v___f_1028_);
return v___x_1054_;
}
}
v___jp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
lean_inc_ref(v___y_1057_);
v___x_1058_ = l_Lean_stringToMessageData(v___y_1057_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1056_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__6);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_MessageData_ofName(v_mod_990_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_Name_isAnonymous(v_hint_992_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__8);
v___x_1066_ = l_Lean_MessageData_ofName(v_hint_992_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___y_1051_ = v___x_1063_;
v___y_1052_ = v___x_1067_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_hint_992_);
v___x_1068_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__9);
v___y_1051_ = v___x_1063_;
v___y_1052_ = v___x_1068_;
goto v___jp_1050_;
}
}
}
v___jp_1030_:
{
lean_object* v___x_1032_; lean_object* v_toEnvExtension_1033_; lean_object* v_env_1034_; lean_object* v_nextMacroScope_1035_; lean_object* v_ngen_1036_; lean_object* v_auxDeclNGen_1037_; lean_object* v_traceState_1038_; lean_object* v_recordedDeps_1039_; lean_object* v_messages_1040_; lean_object* v_infoState_1041_; lean_object* v_snapshotTasks_1042_; lean_object* v_asyncMode_1043_; uint8_t v_logWrites_1044_; lean_object* v___x_1045_; 
v___x_1032_ = lean_st_ref_take(v___y_1031_);
v_toEnvExtension_1033_ = lean_ctor_get(v___x_1019_, 0);
v_env_1034_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1034_);
v_nextMacroScope_1035_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_nextMacroScope_1035_);
v_ngen_1036_ = lean_ctor_get(v___x_1032_, 2);
lean_inc_ref(v_ngen_1036_);
v_auxDeclNGen_1037_ = lean_ctor_get(v___x_1032_, 3);
lean_inc_ref(v_auxDeclNGen_1037_);
v_traceState_1038_ = lean_ctor_get(v___x_1032_, 4);
lean_inc_ref(v_traceState_1038_);
v_recordedDeps_1039_ = lean_ctor_get(v___x_1032_, 6);
lean_inc_ref(v_recordedDeps_1039_);
v_messages_1040_ = lean_ctor_get(v___x_1032_, 7);
lean_inc_ref(v_messages_1040_);
v_infoState_1041_ = lean_ctor_get(v___x_1032_, 8);
lean_inc_ref(v_infoState_1041_);
v_snapshotTasks_1042_ = lean_ctor_get(v___x_1032_, 9);
lean_inc_ref(v_snapshotTasks_1042_);
lean_dec(v___x_1032_);
v_asyncMode_1043_ = lean_ctor_get(v_toEnvExtension_1033_, 2);
v_logWrites_1044_ = lean_ctor_get_uint8(v_toEnvExtension_1033_, sizeof(void*)*6);
v___x_1045_ = lean_box(0);
if (v_logWrites_1044_ == 0)
{
lean_object* v___x_1046_; 
lean_inc_ref(v_toEnvExtension_1033_);
v___x_1046_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1033_, v_env_1034_, v___f_1028_, v_asyncMode_1043_, v___x_1021_, v___x_1029_);
v___y_997_ = v_recordedDeps_1039_;
v___y_998_ = v_ngen_1036_;
v___y_999_ = v___x_1045_;
v___y_1000_ = v_snapshotTasks_1042_;
v___y_1001_ = v_messages_1040_;
v___y_1002_ = v_auxDeclNGen_1037_;
v___y_1003_ = v_traceState_1038_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v_nextMacroScope_1035_;
v___y_1006_ = v_infoState_1041_;
v___y_1007_ = v___x_1046_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref_n(v_toEnvExtension_1033_, 2);
v___x_1047_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1033_, v_env_1034_);
lean_dec_ref(v_env_1034_);
v___x_1048_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1033_, v___x_1047_, v___f_1028_, v_asyncMode_1043_, v___x_1021_, v___x_1029_);
v___y_997_ = v_recordedDeps_1039_;
v___y_998_ = v_ngen_1036_;
v___y_999_ = v___x_1045_;
v___y_1000_ = v_snapshotTasks_1042_;
v___y_1001_ = v_messages_1040_;
v___y_1002_ = v_auxDeclNGen_1037_;
v___y_1003_ = v_traceState_1038_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v_nextMacroScope_1035_;
v___y_1006_ = v_infoState_1041_;
v___y_1007_ = v___x_1048_;
goto v___jp_996_;
}
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec_ref_known(v_entry_1016_, 1);
lean_dec(v_hint_992_);
lean_dec(v_mod_990_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
v___jp_996_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_1009_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1009_, 0, v___y_1007_);
lean_ctor_set(v___x_1009_, 1, v___y_1005_);
lean_ctor_set(v___x_1009_, 2, v___y_998_);
lean_ctor_set(v___x_1009_, 3, v___y_1002_);
lean_ctor_set(v___x_1009_, 4, v___y_1003_);
lean_ctor_set(v___x_1009_, 5, v___x_1008_);
lean_ctor_set(v___x_1009_, 6, v___y_997_);
lean_ctor_set(v___x_1009_, 7, v___y_1001_);
lean_ctor_set(v___x_1009_, 8, v___y_1006_);
lean_ctor_set(v___x_1009_, 9, v___y_1000_);
v___x_1010_ = lean_st_ref_put(v___y_1004_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___y_999_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_mod_1084_, lean_object* v_isMeta_1085_, lean_object* v_hint_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v_isMeta_boxed_1090_; lean_object* v_res_1091_; 
v_isMeta_boxed_1090_ = lean_unbox(v_isMeta_1085_);
v_res_1091_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2(v_mod_1084_, v_isMeta_boxed_1090_, v_hint_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3(lean_object* v___x_1092_, lean_object* v_declName_1093_, lean_object* v_as_1094_, size_t v_sz_1095_, size_t v_i_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_usize_dec_lt(v_i_1096_, v_sz_1095_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v_declName_1093_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_b_1097_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; lean_object* v_modules_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v_toImport_1108_; lean_object* v_module_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1103_ = l_Lean_Environment_header(v___x_1092_);
v_modules_1104_ = lean_ctor_get(v___x_1103_, 3);
lean_inc_ref(v_modules_1104_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1106_ = lean_array_uget_borrowed(v_as_1094_, v_i_1096_);
v___x_1107_ = lean_array_get(v___x_1105_, v_modules_1104_, v_a_1106_);
lean_dec_ref(v_modules_1104_);
v_toImport_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_toImport_1108_);
lean_dec(v___x_1107_);
v_module_1109_ = lean_ctor_get(v_toImport_1108_, 0);
lean_inc(v_module_1109_);
lean_dec_ref(v_toImport_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = 0;
lean_inc(v_declName_1093_);
v___x_1112_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2(v_module_1109_, v___x_1111_, v_declName_1093_, v___y_1098_, v___y_1099_);
if (lean_obj_tag(v___x_1112_) == 0)
{
size_t v___x_1113_; size_t v___x_1114_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_add(v_i_1096_, v___x_1113_);
v_i_1096_ = v___x_1114_;
v_b_1097_ = v___x_1110_;
goto _start;
}
else
{
lean_dec(v_declName_1093_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v___x_1116_, lean_object* v_declName_1117_, lean_object* v_as_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
size_t v_sz_boxed_1125_; size_t v_i_boxed_1126_; lean_object* v_res_1127_; 
v_sz_boxed_1125_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1126_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3(v___x_1116_, v_declName_1117_, v_as_1118_, v_sz_boxed_1125_, v_i_boxed_1126_, v_b_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v_as_1118_);
lean_dec_ref(v___x_1116_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1(lean_object* v_declName_1131_, uint8_t v_isMeta_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_env_1141_; lean_object* v___y_1143_; lean_object* v___x_1156_; 
v___x_1136_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__0);
v___x_1137_ = lean_st_ref_get(v___y_1134_);
v_env_1141_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1137_);
v___x_1156_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1141_, v_declName_1131_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_dec_ref(v_env_1141_);
lean_dec(v_declName_1131_);
goto v___jp_1138_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; lean_object* v_modules_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_val_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Environment_header(v_env_1141_);
v_modules_1159_ = lean_ctor_get(v___x_1158_, 3);
lean_inc_ref(v_modules_1159_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = lean_array_get_size(v_modules_1159_);
v___x_1161_ = lean_nat_dec_lt(v_val_1157_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_dec_ref(v_modules_1159_);
lean_dec(v_val_1157_);
lean_dec_ref(v_env_1141_);
lean_dec(v_declName_1131_);
goto v___jp_1138_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___y_1165_; 
v___x_1162_ = lean_array_fget(v_modules_1159_, v_val_1157_);
lean_dec(v_val_1157_);
lean_dec_ref(v_modules_1159_);
v___x_1163_ = lean_st_ref_get(v___y_1134_);
if (v_isMeta_1132_ == 0)
{
lean_dec(v___x_1163_);
v___y_1165_ = v_isMeta_1132_;
goto v___jp_1164_;
}
else
{
lean_object* v_env_1176_; uint8_t v___x_1177_; 
v_env_1176_ = lean_ctor_get(v___x_1163_, 0);
lean_inc_ref(v_env_1176_);
lean_dec(v___x_1163_);
lean_inc(v_declName_1131_);
v___x_1177_ = l_Lean_isMarkedMeta(v_env_1176_, v_declName_1131_);
if (v___x_1177_ == 0)
{
v___y_1165_ = v_isMeta_1132_;
goto v___jp_1164_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = 0;
v___y_1165_ = v___x_1178_;
goto v___jp_1164_;
}
}
v___jp_1164_:
{
lean_object* v_toImport_1166_; lean_object* v_module_1167_; lean_object* v___x_1168_; 
v_toImport_1166_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_toImport_1166_);
lean_dec(v___x_1162_);
v_module_1167_ = lean_ctor_get(v_toImport_1166_, 0);
lean_inc(v_module_1167_);
lean_dec_ref(v_toImport_1166_);
lean_inc(v_declName_1131_);
v___x_1168_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2(v_module_1167_, v___y_1165_, v_declName_1131_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref_known(v___x_1168_, 1);
v___x_1169_ = l_Lean_indirectModUseExt;
v___x_1170_ = lean_box(1);
v___x_1171_ = lean_box(0);
lean_inc_ref(v_env_1141_);
v___x_1172_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1136_, v___x_1169_, v_env_1141_, v___x_1170_, v___x_1171_);
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg(v___x_1172_, v_declName_1131_);
lean_dec(v___x_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___closed__1));
v___y_1143_ = v___x_1174_;
goto v___jp_1142_;
}
else
{
lean_object* v_val_1175_; 
v_val_1175_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1173_, 1);
v___y_1143_ = v_val_1175_;
goto v___jp_1142_;
}
}
else
{
lean_dec_ref(v_env_1141_);
lean_dec(v_declName_1131_);
return v___x_1168_;
}
}
}
}
v___jp_1138_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; size_t v_sz_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_box(0);
v_sz_1145_ = lean_array_size(v___y_1143_);
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__3(v_env_1141_, v_declName_1131_, v___y_1143_, v_sz_1145_, v___x_1146_, v___x_1144_, v___y_1133_, v___y_1134_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_env_1141_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1147_, 0);
lean_dec(v_unused_1155_);
v___x_1149_ = v___x_1147_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_dec(v___x_1147_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1144_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1144_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1179_, lean_object* v_isMeta_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_isMeta_boxed_1184_; lean_object* v_res_1185_; 
v_isMeta_boxed_1184_ = lean_unbox(v_isMeta_1180_);
v_res_1185_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1(v_declName_1179_, v_isMeta_boxed_1184_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1185_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__0);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(1);
v___x_1195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___closed__4);
v___x_1196_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
lean_ctor_set(v___x_1197_, 2, v___x_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(uint8_t v_x_1198_, lean_object* v_stx_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1294_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1294_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1294_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = l_Lean_Syntax_getId(v_a_1204_);
v___x_1209_ = l_Lean_Name_isAtomic(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = l_Lean_Name_getRoot(v___x_1208_);
v___x_1211_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1212_ = lean_name_eq(v___x_1210_, v___x_1211_);
lean_dec(v___x_1210_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v_a_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1214_ = v___x_1206_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1208_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1246_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1216_ = lean_box(0);
lean_inc(v___x_1208_);
v___x_1217_ = l_Lean_Name_replacePrefix(v___x_1208_, v___x_1211_, v___x_1216_);
v___x_1288_ = lean_box(0);
v___x_1289_ = l_Lean_Syntax_identComponents(v_a_1204_, v___x_1288_);
if (lean_obj_tag(v___x_1289_) == 0)
{
v___y_1246_ = v___x_1289_;
goto v___jp_1245_;
}
else
{
lean_object* v_tail_1290_; 
v_tail_1290_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_tail_1290_);
lean_dec_ref_known(v___x_1289_, 2);
v___y_1246_ = v_tail_1290_;
goto v___jp_1245_;
}
v___jp_1218_:
{
lean_object* v___x_1222_; lean_object* v_env_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_st_ref_get(v___y_1221_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
lean_inc(v___x_1217_);
v___x_1224_ = l_Lean_Environment_contains(v_env_1223_, v___x_1217_, v___x_1212_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1226_; 
lean_dec(v___y_1219_);
lean_dec(v___x_1217_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1226_ = v___x_1206_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1208_);
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
lean_object* v___x_1228_; 
lean_del_object(v___x_1206_);
v___x_1228_ = l_Lean_Core_checkDeprecatedAt(v___y_1219_, v___x_1217_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1208_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1208_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v___x_1208_);
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
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
v___jp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_infoState_1253_; uint8_t v_enabled_1254_; 
v___x_1247_ = lean_array_mk(v___y_1246_);
v___x_1248_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1249_ = lean_box(2);
v___x_1250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
lean_ctor_set(v___x_1250_, 2, v___x_1247_);
lean_inc(v___x_1217_);
v___x_1251_ = l_Lean_mkIdentFrom(v___x_1250_, v___x_1217_, v___x_1212_);
lean_dec_ref_known(v___x_1250_, 3);
v___x_1252_ = lean_st_ref_get(v___y_1201_);
v_infoState_1253_ = lean_ctor_get(v___x_1252_, 8);
lean_inc_ref(v_infoState_1253_);
lean_dec(v___x_1252_);
v_enabled_1254_ = lean_ctor_get_uint8(v_infoState_1253_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1253_);
if (v_enabled_1254_ == 0)
{
v___y_1219_ = v___x_1251_;
v___y_1220_ = v___y_1200_;
v___y_1221_ = v___y_1201_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_);
v___x_1256_ = lean_box(0);
lean_inc(v___x_1217_);
lean_inc(v___x_1251_);
v___x_1257_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1251_);
lean_ctor_set(v___x_1257_, 1, v___x_1217_);
lean_ctor_set(v___x_1257_, 2, v___x_1255_);
lean_ctor_set(v___x_1257_, 3, v___x_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*4, v___x_1209_);
v___x_1258_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0(v___x_1257_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v_env_1260_; uint8_t v___x_1261_; 
lean_dec_ref_known(v___x_1258_, 1);
v___x_1259_ = lean_st_ref_get(v___y_1201_);
v_env_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1259_);
lean_inc(v___x_1217_);
v___x_1261_ = l_Lean_Environment_contains(v_env_1260_, v___x_1217_, v___x_1212_);
if (v___x_1261_ == 0)
{
v___y_1219_ = v___x_1251_;
v___y_1220_ = v___y_1200_;
v___y_1221_ = v___y_1201_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1262_; 
lean_inc(v___x_1217_);
v___x_1262_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1(v___x_1217_, v___x_1209_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1262_, 1);
lean_inc(v___x_1217_);
lean_inc(v___x_1251_);
v___x_1263_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2(v___x_1251_, v___x_1217_, v___x_1256_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_dec_ref_known(v___x_1263_, 1);
v___y_1219_ = v___x_1251_;
v___y_1220_ = v___y_1200_;
v___y_1221_ = v___y_1201_;
goto v___jp_1218_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___x_1251_);
lean_dec(v___x_1217_);
lean_dec(v___x_1208_);
lean_del_object(v___x_1206_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
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
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v___x_1251_);
lean_dec(v___x_1217_);
lean_dec(v___x_1208_);
lean_del_object(v___x_1206_);
v_a_1272_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1262_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1262_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v___x_1251_);
lean_dec(v___x_1217_);
lean_dec(v___x_1208_);
lean_del_object(v___x_1206_);
v_a_1280_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1258_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1258_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1292_; 
lean_dec(v_a_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1292_ = v___x_1206_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1208_);
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
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1203_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1203_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object* v_x_1303_, lean_object* v_stx_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_x_9132__boxed_1308_; lean_object* v_res_1309_; 
v_x_9132__boxed_1308_ = lean_unbox(v_x_1303_);
v_res_1309_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(v_x_9132__boxed_1308_, v_stx_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1343_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1344_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1342_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2____boxed(lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_();
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_t_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_1347_, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_t_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_t_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1357_, lean_object* v_m_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_1358_, v_a_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1361_, lean_object* v_m_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1361_, v_m_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_m_1362_);
return v_res_1364_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_1366_, v_x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_1369_, v_x_1370_, v_x_1371_);
lean_dec_ref(v_x_1371_);
lean_dec_ref(v_x_1370_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1374_, lean_object* v_a_1375_, lean_object* v_x_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_1375_, v_x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_a_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_00_u03b2_1378_, v_a_1379_, v_x_1380_);
lean_dec(v_x_1380_);
lean_dec(v_a_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1382_, lean_object* v_x_1383_, size_t v_x_1384_, lean_object* v_x_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_1383_, v_x_1384_, v_x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
size_t v_x_9482__boxed_1391_; uint8_t v_res_1392_; lean_object* v_r_1393_; 
v_x_9482__boxed_1391_ = lean_unbox_usize(v_x_1389_);
lean_dec(v_x_1389_);
v_res_1392_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1387_, v_x_1388_, v_x_9482__boxed_1391_, v_x_1390_);
lean_dec_ref(v_x_1390_);
lean_dec_ref(v_x_1388_);
v_r_1393_ = lean_box(v_res_1392_);
return v_r_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object* v_00_u03b1_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_constName_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(v_00_u03b1_1400_, v_constName_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1406_, lean_object* v_keys_1407_, lean_object* v_vals_1408_, lean_object* v_heq_1409_, lean_object* v_i_1410_, lean_object* v_k_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_1407_, v_i_1410_, v_k_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1413_, lean_object* v_keys_1414_, lean_object* v_vals_1415_, lean_object* v_heq_1416_, lean_object* v_i_1417_, lean_object* v_k_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(v_00_u03b2_1413_, v_keys_1414_, v_vals_1415_, v_heq_1416_, v_i_1417_, v_k_1418_);
lean_dec_ref(v_k_1418_);
lean_dec_ref(v_vals_1415_);
lean_dec_ref(v_keys_1414_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v_constName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_1422_, v_constName_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_ref_1429_, lean_object* v_constName_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_1428_, v_ref_1429_, v_constName_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v_ref_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1435_, lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v_declHint_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_1436_, v_msg_1437_, v_declHint_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_ref_1444_, lean_object* v_msg_1445_, lean_object* v_declHint_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(v_00_u03b1_1443_, v_ref_1444_, v_msg_1445_, v_declHint_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v_ref_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1451_, lean_object* v_declHint_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1451_, v_declHint_1452_, v___y_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1457_, lean_object* v_declHint_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(v_msg_1457_, v_declHint_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1463_, lean_object* v_ref_1464_, lean_object* v_msg_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_1464_, v_msg_1465_, v___y_1466_, v___y_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_1470_, v_ref_1471_, v_msg_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v_ref_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1478_, v___y_1479_, v___y_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_msg_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1483_, v_msg_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1492_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1493_ = l_Lean_addBuiltinDocString(v___x_1491_, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1523_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1524_ = l_Lean_addBuiltinDeclarationRanges(v___x_1522_, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1555_, uint8_t v___x_1556_, lean_object* v_id_1557_, lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1561_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1555_, v___x_1556_);
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1565_ = lean_string_append(v___x_1563_, v___x_1564_);
v___x_1566_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1557_, v___x_1565_, v___y_1559_, v___y_1560_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_id_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v___x_2296__boxed_1573_; lean_object* v_res_1574_; 
v___x_2296__boxed_1573_ = lean_unbox(v___x_1568_);
v_res_1574_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1567_, v___x_2296__boxed_1573_, v_id_1569_, v_x_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v_x_1570_);
lean_dec(v_id_1569_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1585_ = l_String_toRawSubstring_x27(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___y_1590_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1586_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_x_1586_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec(v_x_1586_);
v___x_1611_ = lean_box(1);
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_a_1588_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; lean_object* v_id_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
v_id_1614_ = l_Lean_Syntax_getArg(v_x_1586_, v___x_1613_);
lean_dec(v_x_1586_);
v___x_1615_ = l_Lean_TSyntax_getId(v_id_1614_);
lean_inc(v___x_1615_);
v___x_1616_ = l_Lean_Macro_resolveGlobalName(v___x_1615_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
if (lean_obj_tag(v_a_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_a_1618_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1616_, 2);
v___x_1619_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1620_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1615_, v___x_1610_);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
v___x_1624_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1614_, v___x_1623_, v_a_1587_, v_a_1618_);
lean_dec(v_id_1614_);
v___y_1590_ = v___x_1624_;
goto v___jp_1589_;
}
else
{
lean_object* v_head_1625_; lean_object* v_snd_1626_; 
v_head_1625_ = lean_ctor_get(v_a_1617_, 0);
v_snd_1626_ = lean_ctor_get(v_head_1625_, 1);
if (lean_obj_tag(v_snd_1626_) == 0)
{
lean_object* v_tail_1627_; 
v_tail_1627_ = lean_ctor_get(v_a_1617_, 1);
if (lean_obj_tag(v_tail_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1653_; 
lean_inc(v_head_1625_);
lean_dec(v___x_1615_);
v_a_1628_ = lean_ctor_get(v___x_1616_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1654_);
v___x_1630_ = v___x_1616_;
v_isShared_1631_ = v_isSharedCheck_1653_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1616_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1653_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_fst_1632_; lean_object* v_quotContext_1633_; lean_object* v_currMacroScope_1634_; lean_object* v_ref_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v_fst_1632_ = lean_ctor_get(v_head_1625_, 0);
lean_inc(v_fst_1632_);
lean_dec(v_head_1625_);
v_quotContext_1633_ = lean_ctor_get(v_a_1587_, 1);
v_currMacroScope_1634_ = lean_ctor_get(v_a_1587_, 2);
v_ref_1635_ = lean_ctor_get(v_a_1587_, 5);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_SourceInfo_fromRef(v_ref_1635_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1639_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1640_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1634_);
lean_inc(v_quotContext_1633_);
v___x_1641_ = l_Lean_addMacroScope(v_quotContext_1633_, v___x_1640_, v_currMacroScope_1634_);
v___x_1642_ = lean_box(0);
lean_inc_n(v___x_1637_, 2);
v___x_1643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1637_);
lean_ctor_set(v___x_1643_, 1, v___x_1639_);
lean_ctor_set(v___x_1643_, 2, v___x_1641_);
lean_ctor_set(v___x_1643_, 3, v___x_1642_);
v___x_1644_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1645_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1646_ = l_Lean_Name_append(v___x_1645_, v_fst_1632_);
v___x_1647_ = l_Lean_mkIdentFrom(v_id_1614_, v___x_1646_, v___x_1610_);
lean_dec(v_id_1614_);
v___x_1648_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1644_, v___x_1647_);
v___x_1649_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1638_, v___x_1643_, v___x_1648_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1649_);
v___x_1651_ = v___x_1630_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1628_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
lean_inc_ref(v_a_1617_);
v_a_1655_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1616_, 2);
v___x_1656_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1615_, v___x_1610_, v_id_1614_, v_a_1617_, v_a_1587_, v_a_1655_);
lean_dec_ref_known(v_a_1617_, 2);
lean_dec(v_id_1614_);
v___y_1590_ = v___x_1656_;
goto v___jp_1589_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
lean_inc_ref(v_a_1617_);
v_a_1657_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1616_, 2);
v___x_1658_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1615_, v___x_1610_, v_id_1614_, v_a_1617_, v_a_1587_, v_a_1657_);
lean_dec_ref_known(v_a_1617_, 2);
lean_dec(v_id_1614_);
v___y_1590_ = v___x_1658_;
goto v___jp_1589_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v___x_1615_);
lean_dec(v_id_1614_);
v_a_1659_ = lean_ctor_get(v___x_1616_, 0);
v_a_1660_ = lean_ctor_get(v___x_1616_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1616_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1616_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
v___jp_1589_:
{
if (lean_obj_tag(v___y_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1591_ = lean_ctor_get(v___y_1590_, 0);
v_a_1592_ = lean_ctor_get(v___y_1590_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___y_1590_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___y_1590_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_inc(v_a_1591_);
lean_dec(v___y_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1600_ = lean_ctor_get(v___y_1590_, 0);
v_a_1601_ = lean_ctor_get(v___y_1590_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___y_1590_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___y_1590_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_inc(v_a_1600_);
lean_dec(v___y_1590_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1600_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1668_, v_a_1669_, v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1672_){
_start:
{
lean_object* v_subExpr_1674_; lean_object* v_expr_1675_; lean_object* v___x_1676_; 
v_subExpr_1674_ = lean_ctor_get(v___y_1672_, 3);
v_expr_1675_ = lean_ctor_get(v_subExpr_1674_, 0);
lean_inc_ref(v_expr_1675_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_expr_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1677_);
lean_dec_ref(v___y_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1680_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1696_, lean_object* v_us_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_1699_ = l_Lean_Name_append(v___x_1698_, v_c_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1700_, lean_object* v_us_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1700_, v_us_1701_);
lean_dec(v_us_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1708_);
lean_dec(v_x_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1820_; 
v___x_1744_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1737_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1820_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1820_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
switch(lean_obj_tag(v_a_1745_))
{
case 0:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1749_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
case 1:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1753_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1753_);
v___x_1755_ = v___x_1747_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
case 2:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1757_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1757_);
v___x_1759_ = v___x_1747_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
case 3:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1761_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1761_);
v___x_1763_ = v___x_1747_;
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
case 4:
{
lean_object* v_declName_1765_; lean_object* v_us_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v_declName_1765_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_declName_1765_);
v_us_1766_ = lean_ctor_get(v_a_1745_, 1);
lean_inc(v_us_1766_);
lean_dec_ref_known(v_a_1745_, 2);
v___x_1767_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1765_, v_us_1766_);
lean_dec(v_us_1766_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1767_);
v___x_1769_ = v___x_1747_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
case 5:
{
lean_object* v_fn_1771_; lean_object* v___x_1772_; 
v_fn_1771_ = lean_ctor_get(v_a_1745_, 0);
lean_inc_ref(v_fn_1771_);
lean_dec_ref_known(v_a_1745_, 2);
v___x_1772_ = l_Lean_Expr_getAppFn(v_fn_1771_);
lean_dec_ref(v_fn_1771_);
if (lean_obj_tag(v___x_1772_) == 4)
{
lean_object* v_declName_1773_; lean_object* v_us_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v_declName_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_declName_1773_);
v_us_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc(v_us_1774_);
lean_dec_ref_known(v___x_1772_, 2);
v___x_1775_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1773_, v_us_1774_);
lean_dec(v_us_1774_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1775_);
v___x_1777_ = v___x_1747_;
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
lean_dec_ref(v___x_1772_);
v___x_1779_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1779_);
v___x_1781_ = v___x_1747_;
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
case 6:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
lean_dec_ref_known(v_a_1745_, 3);
v___x_1783_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1783_);
v___x_1785_ = v___x_1747_;
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
case 7:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec_ref_known(v_a_1745_, 3);
v___x_1787_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1787_);
v___x_1789_ = v___x_1747_;
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
case 8:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_dec_ref_known(v_a_1745_, 4);
v___x_1791_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1791_);
v___x_1793_ = v___x_1747_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
case 9:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec_ref_known(v_a_1745_, 1);
v___x_1795_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1795_);
v___x_1797_ = v___x_1747_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
case 10:
{
lean_object* v_data_1799_; 
v_data_1799_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_data_1799_);
lean_dec_ref_known(v_a_1745_, 2);
if (lean_obj_tag(v_data_1799_) == 1)
{
lean_object* v_tail_1800_; 
v_tail_1800_ = lean_ctor_get(v_data_1799_, 1);
if (lean_obj_tag(v_tail_1800_) == 0)
{
lean_object* v_head_1801_; lean_object* v_fst_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v_head_1801_ = lean_ctor_get(v_data_1799_, 0);
lean_inc(v_head_1801_);
lean_dec_ref_known(v_data_1799_, 2);
v_fst_1802_ = lean_ctor_get(v_head_1801_, 0);
lean_inc(v_fst_1802_);
lean_dec(v_head_1801_);
v___x_1803_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1804_ = l_Lean_Name_append(v___x_1803_, v_fst_1802_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1804_);
v___x_1806_ = v___x_1747_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1799_);
lean_dec_ref_known(v_data_1799_, 2);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1808_);
v___x_1810_ = v___x_1747_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1799_);
lean_dec(v_data_1799_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1812_);
v___x_1814_ = v___x_1747_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
default: 
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec_ref_known(v_a_1745_, 3);
v___x_1816_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1816_);
v___x_1818_ = v___x_1747_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1829_, lean_object* v_k_1830_, lean_object* v_v_1831_){
_start:
{
lean_object* v_map_1832_; uint8_t v_hasTrace_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1846_; 
v_map_1832_ = lean_ctor_get(v_o_1829_, 0);
v_hasTrace_1833_ = lean_ctor_get_uint8(v_o_1829_, sizeof(void*)*1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_o_1829_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1835_ = v_o_1829_;
v_isShared_1836_ = v_isSharedCheck_1846_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_map_1832_);
lean_dec(v_o_1829_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1846_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; 
lean_inc(v_k_1830_);
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1830_, v_v_1831_, v_map_1832_);
if (v_hasTrace_1833_ == 0)
{
lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_1839_ = l_Lean_Name_isPrefixOf(v___x_1838_, v_k_1830_);
lean_dec(v_k_1830_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1841_ = v___x_1835_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1837_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*1, v___x_1839_);
return v___x_1841_;
}
}
else
{
lean_object* v___x_1844_; 
lean_dec(v_k_1830_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1844_ = v___x_1835_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1845_, sizeof(void*)*1, v_hasTrace_1833_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1847_){
_start:
{
lean_object* v_subExpr_1849_; lean_object* v_pos_1850_; lean_object* v___x_1851_; 
v_subExpr_1849_ = lean_ctor_get(v___y_1847_, 3);
v_pos_1850_ = lean_ctor_get(v_subExpr_1849_, 1);
lean_inc(v_pos_1850_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_pos_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1852_);
lean_dec_ref(v___y_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1855_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1871_, lean_object* v_k_1872_){
_start:
{
if (lean_obj_tag(v_t_1871_) == 0)
{
lean_object* v_k_1873_; lean_object* v_v_1874_; lean_object* v_l_1875_; lean_object* v_r_1876_; uint8_t v___x_1877_; 
v_k_1873_ = lean_ctor_get(v_t_1871_, 1);
v_v_1874_ = lean_ctor_get(v_t_1871_, 2);
v_l_1875_ = lean_ctor_get(v_t_1871_, 3);
v_r_1876_ = lean_ctor_get(v_t_1871_, 4);
v___x_1877_ = lean_nat_dec_lt(v_k_1872_, v_k_1873_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_nat_dec_eq(v_k_1872_, v_k_1873_);
if (v___x_1878_ == 0)
{
v_t_1871_ = v_r_1876_;
goto _start;
}
else
{
lean_object* v___x_1880_; 
lean_inc(v_v_1874_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_v_1874_);
return v___x_1880_;
}
}
else
{
v_t_1871_ = v_l_1875_;
goto _start;
}
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_box(0);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1883_, lean_object* v_k_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1883_, v_k_1884_);
lean_dec(v_k_1884_);
lean_dec(v_t_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v_k_1889_; lean_object* v_v_1890_; lean_object* v_l_1891_; lean_object* v_r_1892_; lean_object* v___x_1893_; lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1896_; 
v_k_1889_ = lean_ctor_get(v_x_1887_, 1);
lean_inc(v_k_1889_);
v_v_1890_ = lean_ctor_get(v_x_1887_, 2);
lean_inc(v_v_1890_);
v_l_1891_ = lean_ctor_get(v_x_1887_, 3);
lean_inc(v_l_1891_);
v_r_1892_ = lean_ctor_get(v_x_1887_, 4);
lean_inc(v_r_1892_);
lean_dec_ref_known(v_x_1887_, 5);
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1886_, v_l_1891_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1893_);
v_a_1895_ = lean_ctor_get(v_a_1894_, 0);
lean_inc(v_a_1895_);
lean_dec(v_a_1894_);
v___x_1896_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1895_, v_k_1889_, v_v_1890_);
v_init_1886_ = v___x_1896_;
v_x_1887_ = v_r_1892_;
goto _start;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_init_1886_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1900_, lean_object* v_x_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1900_, v_x_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1934_; 
v___x_1911_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1908_);
v___x_1912_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1904_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1934_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1934_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_optionsPerPos_1917_; lean_object* v___x_1918_; 
v_optionsPerPos_1917_ = lean_ctor_get(v_a_1904_, 0);
v___x_1918_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1917_, v_a_1913_);
lean_dec(v_a_1913_);
if (lean_obj_tag(v___x_1918_) == 1)
{
lean_object* v_val_1919_; lean_object* v_map_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
lean_del_object(v___x_1915_);
v_val_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_map_1920_ = lean_ctor_get(v_val_1919_, 0);
lean_inc(v_map_1920_);
lean_dec(v_val_1919_);
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v___x_1911_, v_map_1920_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_a_1926_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_a_1926_);
lean_dec(v_a_1922_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_a_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v___x_1918_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1911_);
v___x_1932_ = v___x_1915_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1911_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1943_, lean_object* v_t_1944_, lean_object* v_k_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1944_, v_k_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1947_, lean_object* v_t_1948_, lean_object* v_k_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1947_, v_t_1948_, v_k_1949_);
lean_dec(v_k_1949_);
lean_dec(v_t_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1951_, lean_object* v_x_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1951_, v_x_1952_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1961_, v_x_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_apply_1(v_opt_1971_, v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_opt_1971_);
v_a_1989_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1979_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1979_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_2006_, lean_object* v_opt_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_2016_, lean_object* v_opt_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_2016_, v_opt_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_2026_, lean_object* v_d_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2026_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; uint8_t v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = lean_unbox(v_a_2036_);
lean_dec(v_a_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_dec_ref(v_d_2027_);
v___x_2038_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; 
lean_inc(v_a_2033_);
lean_inc_ref(v_a_2032_);
lean_inc(v_a_2031_);
lean_inc_ref(v_a_2030_);
lean_inc(v_a_2029_);
lean_inc_ref(v_a_2028_);
v___x_2039_ = lean_apply_7(v_d_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, lean_box(0));
return v___x_2039_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_d_2027_);
v_a_2040_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2035_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2035_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2048_, lean_object* v_d_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2048_, v_d_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2058_, lean_object* v_d_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2058_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; uint8_t v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = lean_unbox(v_a_2068_);
lean_dec(v_a_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
lean_inc(v_a_2065_);
lean_inc_ref(v_a_2064_);
lean_inc(v_a_2063_);
lean_inc_ref(v_a_2062_);
lean_inc(v_a_2061_);
lean_inc_ref(v_a_2060_);
v___x_2070_ = lean_apply_7(v_d_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, lean_box(0));
return v___x_2070_;
}
else
{
lean_object* v___x_2071_; 
lean_dec_ref(v_d_2059_);
v___x_2071_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2071_;
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_d_2059_);
v_a_2072_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2067_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2080_, lean_object* v_d_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2080_, v_d_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2090_, lean_object* v_v_2091_, lean_object* v_t_2092_){
_start:
{
if (lean_obj_tag(v_t_2092_) == 0)
{
lean_object* v_size_2093_; lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v_l_2096_; lean_object* v_r_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2378_; 
v_size_2093_ = lean_ctor_get(v_t_2092_, 0);
v_k_2094_ = lean_ctor_get(v_t_2092_, 1);
v_v_2095_ = lean_ctor_get(v_t_2092_, 2);
v_l_2096_ = lean_ctor_get(v_t_2092_, 3);
v_r_2097_ = lean_ctor_get(v_t_2092_, 4);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_t_2092_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2099_ = v_t_2092_;
v_isShared_2100_ = v_isSharedCheck_2378_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_r_2097_);
lean_inc(v_l_2096_);
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
lean_inc(v_size_2093_);
lean_dec(v_t_2092_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2378_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_nat_dec_lt(v_k_2090_, v_k_2094_);
if (v___x_2101_ == 0)
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_nat_dec_eq(v_k_2090_, v_k_2094_);
if (v___x_2102_ == 0)
{
lean_object* v_impl_2103_; lean_object* v___x_2104_; 
lean_dec(v_size_2093_);
v_impl_2103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2090_, v_v_2091_, v_r_2097_);
v___x_2104_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2105_; lean_object* v_size_2106_; lean_object* v_k_2107_; lean_object* v_v_2108_; lean_object* v_l_2109_; lean_object* v_r_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_size_2105_ = lean_ctor_get(v_l_2096_, 0);
v_size_2106_ = lean_ctor_get(v_impl_2103_, 0);
v_k_2107_ = lean_ctor_get(v_impl_2103_, 1);
v_v_2108_ = lean_ctor_get(v_impl_2103_, 2);
v_l_2109_ = lean_ctor_get(v_impl_2103_, 3);
lean_inc(v_l_2109_);
v_r_2110_ = lean_ctor_get(v_impl_2103_, 4);
v___x_2111_ = lean_unsigned_to_nat(3u);
v___x_2112_ = lean_nat_mul(v___x_2111_, v_size_2105_);
v___x_2113_ = lean_nat_dec_lt(v___x_2112_, v_size_2106_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_l_2109_);
v___x_2114_ = lean_nat_add(v___x_2104_, v_size_2105_);
v___x_2115_ = lean_nat_add(v___x_2114_, v_size_2106_);
lean_dec(v___x_2114_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_impl_2103_);
lean_ctor_set(v___x_2099_, 0, v___x_2115_);
v___x_2117_ = v___x_2099_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_l_2096_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_impl_2103_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
else
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2182_; 
lean_inc(v_r_2110_);
lean_inc(v_v_2108_);
lean_inc(v_k_2107_);
lean_inc(v_size_2106_);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_impl_2103_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2183_ = lean_ctor_get(v_impl_2103_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_impl_2103_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_impl_2103_, 2);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_impl_2103_, 1);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_impl_2103_, 0);
lean_dec(v_unused_2187_);
v___x_2120_ = v_impl_2103_;
v_isShared_2121_ = v_isSharedCheck_2182_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v_impl_2103_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2182_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_size_2122_; lean_object* v_k_2123_; lean_object* v_v_2124_; lean_object* v_l_2125_; lean_object* v_r_2126_; lean_object* v_size_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_size_2122_ = lean_ctor_get(v_l_2109_, 0);
v_k_2123_ = lean_ctor_get(v_l_2109_, 1);
v_v_2124_ = lean_ctor_get(v_l_2109_, 2);
v_l_2125_ = lean_ctor_get(v_l_2109_, 3);
v_r_2126_ = lean_ctor_get(v_l_2109_, 4);
v_size_2127_ = lean_ctor_get(v_r_2110_, 0);
v___x_2128_ = lean_unsigned_to_nat(2u);
v___x_2129_ = lean_nat_mul(v___x_2128_, v_size_2127_);
v___x_2130_ = lean_nat_dec_lt(v_size_2122_, v___x_2129_);
lean_dec(v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2158_; 
lean_inc(v_r_2126_);
lean_inc(v_l_2125_);
lean_inc(v_v_2124_);
lean_inc(v_k_2123_);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_l_2109_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2159_ = lean_ctor_get(v_l_2109_, 4);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_l_2109_, 3);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_l_2109_, 2);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_l_2109_, 1);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_l_2109_, 0);
lean_dec(v_unused_2163_);
v___x_2132_ = v_l_2109_;
v_isShared_2133_ = v_isSharedCheck_2158_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_l_2109_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2158_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2148_; 
v___x_2134_ = lean_nat_add(v___x_2104_, v_size_2105_);
v___x_2135_ = lean_nat_add(v___x_2134_, v_size_2106_);
lean_dec(v_size_2106_);
if (lean_obj_tag(v_l_2125_) == 0)
{
lean_object* v_size_2156_; 
v_size_2156_ = lean_ctor_get(v_l_2125_, 0);
lean_inc(v_size_2156_);
v___y_2148_ = v_size_2156_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___y_2148_ = v___x_2157_;
goto v___jp_2147_;
}
v___jp_2136_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_nat_add(v___y_2137_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec(v___y_2137_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v_r_2110_);
lean_ctor_set(v___x_2132_, 3, v_r_2126_);
lean_ctor_set(v___x_2132_, 2, v_v_2108_);
lean_ctor_set(v___x_2132_, 1, v_k_2107_);
lean_ctor_set(v___x_2132_, 0, v___x_2140_);
v___x_2142_ = v___x_2132_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2107_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2108_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_r_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_r_2110_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v___x_2142_);
lean_ctor_set(v___x_2120_, 3, v___y_2138_);
lean_ctor_set(v___x_2120_, 2, v_v_2124_);
lean_ctor_set(v___x_2120_, 1, v_k_2123_);
lean_ctor_set(v___x_2120_, 0, v___x_2135_);
v___x_2144_ = v___x_2120_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2123_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2124_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v___y_2138_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
v___jp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_nat_add(v___x_2134_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec(v___x_2134_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_l_2125_);
lean_ctor_set(v___x_2099_, 0, v___x_2149_);
v___x_2151_ = v___x_2099_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_l_2096_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_l_2125_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_nat_add(v___x_2104_, v_size_2127_);
if (lean_obj_tag(v_r_2126_) == 0)
{
lean_object* v_size_2153_; 
v_size_2153_ = lean_ctor_get(v_r_2126_, 0);
lean_inc(v_size_2153_);
v___y_2137_ = v___x_2152_;
v___y_2138_ = v___x_2151_;
v___y_2139_ = v_size_2153_;
goto v___jp_2136_;
}
else
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___y_2137_ = v___x_2152_;
v___y_2138_ = v___x_2151_;
v___y_2139_ = v___x_2154_;
goto v___jp_2136_;
}
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_del_object(v___x_2099_);
v___x_2164_ = lean_nat_add(v___x_2104_, v_size_2105_);
v___x_2165_ = lean_nat_add(v___x_2164_, v_size_2106_);
lean_dec(v_size_2106_);
v___x_2166_ = lean_nat_add(v___x_2164_, v_size_2122_);
lean_dec(v___x_2164_);
lean_inc_ref(v_l_2096_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_l_2109_);
lean_ctor_set(v___x_2120_, 3, v_l_2096_);
lean_ctor_set(v___x_2120_, 2, v_v_2095_);
lean_ctor_set(v___x_2120_, 1, v_k_2094_);
lean_ctor_set(v___x_2120_, 0, v___x_2166_);
v___x_2168_ = v___x_2120_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_l_2096_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_l_2109_);
v___x_2168_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_isSharedCheck_2175_ = !lean_is_exclusive(v_l_2096_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2176_ = lean_ctor_get(v_l_2096_, 4);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_l_2096_, 3);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_l_2096_, 2);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_l_2096_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_l_2096_, 0);
lean_dec(v_unused_2180_);
v___x_2170_ = v_l_2096_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v_l_2096_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 4, v_r_2110_);
lean_ctor_set(v___x_2170_, 3, v___x_2168_);
lean_ctor_set(v___x_2170_, 2, v_v_2108_);
lean_ctor_set(v___x_2170_, 1, v_k_2107_);
lean_ctor_set(v___x_2170_, 0, v___x_2165_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2107_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2108_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_r_2110_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2188_; 
v_l_2188_ = lean_ctor_get(v_impl_2103_, 3);
lean_inc(v_l_2188_);
if (lean_obj_tag(v_l_2188_) == 0)
{
lean_object* v_r_2189_; lean_object* v_k_2190_; lean_object* v_v_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2214_; 
v_r_2189_ = lean_ctor_get(v_impl_2103_, 4);
v_k_2190_ = lean_ctor_get(v_impl_2103_, 1);
v_v_2191_ = lean_ctor_get(v_impl_2103_, 2);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_impl_2103_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2215_ = lean_ctor_get(v_impl_2103_, 3);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_impl_2103_, 0);
lean_dec(v_unused_2216_);
v___x_2193_ = v_impl_2103_;
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_r_2189_);
lean_inc(v_v_2191_);
lean_inc(v_k_2190_);
lean_dec(v_impl_2103_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_k_2195_; lean_object* v_v_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2210_; 
v_k_2195_ = lean_ctor_get(v_l_2188_, 1);
v_v_2196_ = lean_ctor_get(v_l_2188_, 2);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_l_2188_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; 
v_unused_2211_ = lean_ctor_get(v_l_2188_, 4);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_l_2188_, 3);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_l_2188_, 0);
lean_dec(v_unused_2213_);
v___x_2198_ = v_l_2188_;
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_v_2196_);
lean_inc(v_k_2195_);
lean_dec(v_l_2188_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2189_, 2);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v_r_2189_);
lean_ctor_set(v___x_2198_, 3, v_r_2189_);
lean_ctor_set(v___x_2198_, 2, v_v_2095_);
lean_ctor_set(v___x_2198_, 1, v_k_2094_);
lean_ctor_set(v___x_2198_, 0, v___x_2104_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_r_2189_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_r_2189_);
v___x_2202_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2204_; 
lean_inc(v_r_2189_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 3, v_r_2189_);
lean_ctor_set(v___x_2193_, 0, v___x_2104_);
v___x_2204_ = v___x_2193_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_r_2189_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_r_2189_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v___x_2204_);
lean_ctor_set(v___x_2099_, 3, v___x_2202_);
lean_ctor_set(v___x_2099_, 2, v_v_2196_);
lean_ctor_set(v___x_2099_, 1, v_k_2195_);
lean_ctor_set(v___x_2099_, 0, v___x_2200_);
v___x_2206_ = v___x_2099_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_2195_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2196_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v_r_2217_; 
v_r_2217_ = lean_ctor_get(v_impl_2103_, 4);
lean_inc(v_r_2217_);
if (lean_obj_tag(v_r_2217_) == 0)
{
lean_object* v_k_2218_; lean_object* v_v_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
v_k_2218_ = lean_ctor_get(v_impl_2103_, 1);
v_v_2219_ = lean_ctor_get(v_impl_2103_, 2);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_impl_2103_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; 
v_unused_2231_ = lean_ctor_get(v_impl_2103_, 4);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_impl_2103_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_impl_2103_, 0);
lean_dec(v_unused_2233_);
v___x_2221_ = v_impl_2103_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_v_2219_);
lean_inc(v_k_2218_);
lean_dec(v_impl_2103_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_unsigned_to_nat(3u);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 4, v_l_2188_);
lean_ctor_set(v___x_2221_, 2, v_v_2095_);
lean_ctor_set(v___x_2221_, 1, v_k_2094_);
lean_ctor_set(v___x_2221_, 0, v___x_2104_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_l_2188_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_l_2188_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_r_2217_);
lean_ctor_set(v___x_2099_, 3, v___x_2225_);
lean_ctor_set(v___x_2099_, 2, v_v_2219_);
lean_ctor_set(v___x_2099_, 1, v_k_2218_);
lean_ctor_set(v___x_2099_, 0, v___x_2223_);
v___x_2227_ = v___x_2099_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2218_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2219_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_r_2217_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_unsigned_to_nat(2u);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_impl_2103_);
lean_ctor_set(v___x_2099_, 3, v_r_2217_);
lean_ctor_set(v___x_2099_, 0, v___x_2234_);
v___x_2236_ = v___x_2099_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_r_2217_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_impl_2103_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; 
lean_dec(v_v_2095_);
lean_dec(v_k_2094_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 2, v_v_2091_);
lean_ctor_set(v___x_2099_, 1, v_k_2090_);
v___x_2239_ = v___x_2099_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_size_2093_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_k_2090_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_v_2091_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_l_2096_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_r_2097_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_impl_2241_; lean_object* v___x_2242_; 
lean_dec(v_size_2093_);
v_impl_2241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2090_, v_v_2091_, v_l_2096_);
v___x_2242_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2097_) == 0)
{
lean_object* v_size_2243_; lean_object* v_size_2244_; lean_object* v_k_2245_; lean_object* v_v_2246_; lean_object* v_l_2247_; lean_object* v_r_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_size_2243_ = lean_ctor_get(v_r_2097_, 0);
v_size_2244_ = lean_ctor_get(v_impl_2241_, 0);
v_k_2245_ = lean_ctor_get(v_impl_2241_, 1);
v_v_2246_ = lean_ctor_get(v_impl_2241_, 2);
v_l_2247_ = lean_ctor_get(v_impl_2241_, 3);
v_r_2248_ = lean_ctor_get(v_impl_2241_, 4);
lean_inc(v_r_2248_);
v___x_2249_ = lean_unsigned_to_nat(3u);
v___x_2250_ = lean_nat_mul(v___x_2249_, v_size_2243_);
v___x_2251_ = lean_nat_dec_lt(v___x_2250_, v_size_2244_);
lean_dec(v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
lean_dec(v_r_2248_);
v___x_2252_ = lean_nat_add(v___x_2242_, v_size_2244_);
v___x_2253_ = lean_nat_add(v___x_2252_, v_size_2243_);
lean_dec(v___x_2252_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 3, v_impl_2241_);
lean_ctor_set(v___x_2099_, 0, v___x_2253_);
v___x_2255_ = v___x_2099_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_impl_2241_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_r_2097_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
else
{
lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2322_; 
lean_inc(v_l_2247_);
lean_inc(v_v_2246_);
lean_inc(v_k_2245_);
lean_inc(v_size_2244_);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_impl_2241_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; lean_object* v_unused_2324_; lean_object* v_unused_2325_; lean_object* v_unused_2326_; lean_object* v_unused_2327_; 
v_unused_2323_ = lean_ctor_get(v_impl_2241_, 4);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_impl_2241_, 3);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_impl_2241_, 2);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_impl_2241_, 1);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_impl_2241_, 0);
lean_dec(v_unused_2327_);
v___x_2258_ = v_impl_2241_;
v_isShared_2259_ = v_isSharedCheck_2322_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v_impl_2241_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2322_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_size_2260_; lean_object* v_size_2261_; lean_object* v_k_2262_; lean_object* v_v_2263_; lean_object* v_l_2264_; lean_object* v_r_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_size_2260_ = lean_ctor_get(v_l_2247_, 0);
v_size_2261_ = lean_ctor_get(v_r_2248_, 0);
v_k_2262_ = lean_ctor_get(v_r_2248_, 1);
v_v_2263_ = lean_ctor_get(v_r_2248_, 2);
v_l_2264_ = lean_ctor_get(v_r_2248_, 3);
v_r_2265_ = lean_ctor_get(v_r_2248_, 4);
v___x_2266_ = lean_unsigned_to_nat(2u);
v___x_2267_ = lean_nat_mul(v___x_2266_, v_size_2260_);
v___x_2268_ = lean_nat_dec_lt(v_size_2261_, v___x_2267_);
lean_dec(v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2297_; 
lean_inc(v_r_2265_);
lean_inc(v_l_2264_);
lean_inc(v_v_2263_);
lean_inc(v_k_2262_);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_r_2248_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; lean_object* v_unused_2301_; lean_object* v_unused_2302_; 
v_unused_2298_ = lean_ctor_get(v_r_2248_, 4);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_r_2248_, 3);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_r_2248_, 2);
lean_dec(v_unused_2300_);
v_unused_2301_ = lean_ctor_get(v_r_2248_, 1);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_r_2248_, 0);
lean_dec(v_unused_2302_);
v___x_2270_ = v_r_2248_;
v_isShared_2271_ = v_isSharedCheck_2297_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v_r_2248_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2297_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___x_2285_; lean_object* v___y_2287_; 
v___x_2272_ = lean_nat_add(v___x_2242_, v_size_2244_);
lean_dec(v_size_2244_);
v___x_2273_ = lean_nat_add(v___x_2272_, v_size_2243_);
lean_dec(v___x_2272_);
v___x_2285_ = lean_nat_add(v___x_2242_, v_size_2260_);
if (lean_obj_tag(v_l_2264_) == 0)
{
lean_object* v_size_2295_; 
v_size_2295_ = lean_ctor_get(v_l_2264_, 0);
lean_inc(v_size_2295_);
v___y_2287_ = v_size_2295_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v___y_2287_ = v___x_2296_;
goto v___jp_2286_;
}
v___jp_2274_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_nat_add(v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec(v___y_2276_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 4, v_r_2097_);
lean_ctor_set(v___x_2270_, 3, v_r_2265_);
lean_ctor_set(v___x_2270_, 2, v_v_2095_);
lean_ctor_set(v___x_2270_, 1, v_k_2094_);
lean_ctor_set(v___x_2270_, 0, v___x_2278_);
v___x_2280_ = v___x_2270_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_r_2265_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_r_2097_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 4, v___x_2280_);
lean_ctor_set(v___x_2258_, 3, v___y_2275_);
lean_ctor_set(v___x_2258_, 2, v_v_2263_);
lean_ctor_set(v___x_2258_, 1, v_k_2262_);
lean_ctor_set(v___x_2258_, 0, v___x_2273_);
v___x_2282_ = v___x_2258_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v___y_2275_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = lean_nat_add(v___x_2285_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec(v___x_2285_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_l_2264_);
lean_ctor_set(v___x_2099_, 3, v_l_2247_);
lean_ctor_set(v___x_2099_, 2, v_v_2246_);
lean_ctor_set(v___x_2099_, 1, v_k_2245_);
lean_ctor_set(v___x_2099_, 0, v___x_2288_);
v___x_2290_ = v___x_2099_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_k_2245_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_v_2246_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_l_2247_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_l_2264_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_nat_add(v___x_2242_, v_size_2243_);
if (lean_obj_tag(v_r_2265_) == 0)
{
lean_object* v_size_2292_; 
v_size_2292_ = lean_ctor_get(v_r_2265_, 0);
lean_inc(v_size_2292_);
v___y_2275_ = v___x_2290_;
v___y_2276_ = v___x_2291_;
v___y_2277_ = v_size_2292_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___y_2275_ = v___x_2290_;
v___y_2276_ = v___x_2291_;
v___y_2277_ = v___x_2293_;
goto v___jp_2274_;
}
}
}
}
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_del_object(v___x_2099_);
v___x_2303_ = lean_nat_add(v___x_2242_, v_size_2244_);
lean_dec(v_size_2244_);
v___x_2304_ = lean_nat_add(v___x_2303_, v_size_2243_);
lean_dec(v___x_2303_);
v___x_2305_ = lean_nat_add(v___x_2242_, v_size_2243_);
v___x_2306_ = lean_nat_add(v___x_2305_, v_size_2261_);
lean_dec(v___x_2305_);
lean_inc_ref(v_r_2097_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 4, v_r_2097_);
lean_ctor_set(v___x_2258_, 3, v_r_2248_);
lean_ctor_set(v___x_2258_, 2, v_v_2095_);
lean_ctor_set(v___x_2258_, 1, v_k_2094_);
lean_ctor_set(v___x_2258_, 0, v___x_2306_);
v___x_2308_ = v___x_2258_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_r_2248_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_r_2097_);
v___x_2308_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_isSharedCheck_2315_ = !lean_is_exclusive(v_r_2097_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; lean_object* v_unused_2317_; lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; 
v_unused_2316_ = lean_ctor_get(v_r_2097_, 4);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_r_2097_, 3);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_r_2097_, 2);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_r_2097_, 1);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_r_2097_, 0);
lean_dec(v_unused_2320_);
v___x_2310_ = v_r_2097_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_r_2097_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 4, v___x_2308_);
lean_ctor_set(v___x_2310_, 3, v_l_2247_);
lean_ctor_set(v___x_2310_, 2, v_v_2246_);
lean_ctor_set(v___x_2310_, 1, v_k_2245_);
lean_ctor_set(v___x_2310_, 0, v___x_2304_);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_k_2245_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_v_2246_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_l_2247_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v___x_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2328_; 
v_l_2328_ = lean_ctor_get(v_impl_2241_, 3);
if (lean_obj_tag(v_l_2328_) == 0)
{
lean_object* v_r_2329_; lean_object* v_k_2330_; lean_object* v_v_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2342_; 
lean_inc_ref(v_l_2328_);
v_r_2329_ = lean_ctor_get(v_impl_2241_, 4);
v_k_2330_ = lean_ctor_get(v_impl_2241_, 1);
v_v_2331_ = lean_ctor_get(v_impl_2241_, 2);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_impl_2241_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; lean_object* v_unused_2344_; 
v_unused_2343_ = lean_ctor_get(v_impl_2241_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_impl_2241_, 0);
lean_dec(v_unused_2344_);
v___x_2333_ = v_impl_2241_;
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_r_2329_);
lean_inc(v_v_2331_);
lean_inc(v_k_2330_);
lean_dec(v_impl_2241_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2329_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 3, v_r_2329_);
lean_ctor_set(v___x_2333_, 2, v_v_2095_);
lean_ctor_set(v___x_2333_, 1, v_k_2094_);
lean_ctor_set(v___x_2333_, 0, v___x_2242_);
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_r_2329_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_r_2329_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v___x_2337_);
lean_ctor_set(v___x_2099_, 3, v_l_2328_);
lean_ctor_set(v___x_2099_, 2, v_v_2331_);
lean_ctor_set(v___x_2099_, 1, v_k_2330_);
lean_ctor_set(v___x_2099_, 0, v___x_2335_);
v___x_2339_ = v___x_2099_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_k_2330_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_v_2331_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_l_2328_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_r_2345_; 
v_r_2345_ = lean_ctor_get(v_impl_2241_, 4);
lean_inc(v_r_2345_);
if (lean_obj_tag(v_r_2345_) == 0)
{
lean_object* v_k_2346_; lean_object* v_v_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2370_; 
lean_inc(v_l_2328_);
v_k_2346_ = lean_ctor_get(v_impl_2241_, 1);
v_v_2347_ = lean_ctor_get(v_impl_2241_, 2);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_impl_2241_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2371_ = lean_ctor_get(v_impl_2241_, 4);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_impl_2241_, 3);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_impl_2241_, 0);
lean_dec(v_unused_2373_);
v___x_2349_ = v_impl_2241_;
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_v_2347_);
lean_inc(v_k_2346_);
lean_dec(v_impl_2241_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_k_2351_; lean_object* v_v_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2366_; 
v_k_2351_ = lean_ctor_get(v_r_2345_, 1);
v_v_2352_ = lean_ctor_get(v_r_2345_, 2);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_r_2345_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; lean_object* v_unused_2368_; lean_object* v_unused_2369_; 
v_unused_2367_ = lean_ctor_get(v_r_2345_, 4);
lean_dec(v_unused_2367_);
v_unused_2368_ = lean_ctor_get(v_r_2345_, 3);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_r_2345_, 0);
lean_dec(v_unused_2369_);
v___x_2354_ = v_r_2345_;
v_isShared_2355_ = v_isSharedCheck_2366_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_v_2352_);
lean_inc(v_k_2351_);
lean_dec(v_r_2345_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2366_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_unsigned_to_nat(3u);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 4, v_l_2328_);
lean_ctor_set(v___x_2354_, 3, v_l_2328_);
lean_ctor_set(v___x_2354_, 2, v_v_2347_);
lean_ctor_set(v___x_2354_, 1, v_k_2346_);
lean_ctor_set(v___x_2354_, 0, v___x_2242_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2346_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2347_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_l_2328_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_l_2328_);
v___x_2358_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_l_2328_);
lean_ctor_set(v___x_2349_, 2, v_v_2095_);
lean_ctor_set(v___x_2349_, 1, v_k_2094_);
lean_ctor_set(v___x_2349_, 0, v___x_2242_);
v___x_2360_ = v___x_2349_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_l_2328_);
lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_l_2328_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v___x_2360_);
lean_ctor_set(v___x_2099_, 3, v___x_2358_);
lean_ctor_set(v___x_2099_, 2, v_v_2352_);
lean_ctor_set(v___x_2099_, 1, v_k_2351_);
lean_ctor_set(v___x_2099_, 0, v___x_2356_);
v___x_2362_ = v___x_2099_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_k_2351_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_v_2352_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_unsigned_to_nat(2u);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_r_2345_);
lean_ctor_set(v___x_2099_, 3, v_impl_2241_);
lean_ctor_set(v___x_2099_, 0, v___x_2374_);
v___x_2376_ = v___x_2099_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_impl_2241_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_r_2345_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_k_2090_);
lean_ctor_set(v___x_2380_, 2, v_v_2091_);
lean_ctor_set(v___x_2380_, 3, v_t_2092_);
lean_ctor_set(v___x_2380_, 4, v_t_2092_);
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2381_, lean_object* v_v_2382_, lean_object* v_x_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v_a_2392_; lean_object* v_optionsPerPos_2393_; lean_object* v_currNamespace_2394_; lean_object* v_openDecls_2395_; uint8_t v_inPattern_2396_; lean_object* v_subExpr_2397_; lean_object* v_depth_2398_; lean_object* v_lctxInitIndices_2399_; lean_object* v___y_2401_; lean_object* v___x_2406_; 
v___x_2391_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2384_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
v_optionsPerPos_2393_ = lean_ctor_get(v_a_2384_, 0);
v_currNamespace_2394_ = lean_ctor_get(v_a_2384_, 1);
v_openDecls_2395_ = lean_ctor_get(v_a_2384_, 2);
v_inPattern_2396_ = lean_ctor_get_uint8(v_a_2384_, sizeof(void*)*6);
v_subExpr_2397_ = lean_ctor_get(v_a_2384_, 3);
v_depth_2398_ = lean_ctor_get(v_a_2384_, 4);
v_lctxInitIndices_2399_ = lean_ctor_get(v_a_2384_, 5);
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2393_, v_a_2392_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Options_empty;
v___y_2401_ = v___x_2407_;
goto v___jp_2400_;
}
else
{
lean_object* v_val_2408_; 
v_val_2408_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v___x_2406_, 1);
v___y_2401_ = v_val_2408_;
goto v___jp_2400_;
}
v___jp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2401_, v_k_2381_, v_v_2382_);
lean_inc(v_optionsPerPos_2393_);
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2392_, v___x_2402_, v_optionsPerPos_2393_);
lean_inc(v_lctxInitIndices_2399_);
lean_inc(v_depth_2398_);
lean_inc_ref(v_subExpr_2397_);
lean_inc(v_openDecls_2395_);
lean_inc(v_currNamespace_2394_);
v___x_2404_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_currNamespace_2394_);
lean_ctor_set(v___x_2404_, 2, v_openDecls_2395_);
lean_ctor_set(v___x_2404_, 3, v_subExpr_2397_);
lean_ctor_set(v___x_2404_, 4, v_depth_2398_);
lean_ctor_set(v___x_2404_, 5, v_lctxInitIndices_2399_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*6, v_inPattern_2396_);
lean_inc(v_a_2389_);
lean_inc_ref(v_a_2388_);
lean_inc(v_a_2387_);
lean_inc_ref(v_a_2386_);
lean_inc(v_a_2385_);
v___x_2405_ = lean_apply_7(v_x_2383_, v___x_2404_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, lean_box(0));
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2409_, lean_object* v_v_2410_, lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2409_, v_v_2410_, v_x_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2420_, lean_object* v_k_2421_, lean_object* v_v_2422_, lean_object* v_x_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2421_, v_v_2422_, v_x_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_k_2433_, lean_object* v_v_2434_, lean_object* v_x_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2432_, v_k_2433_, v_v_2434_, v_x_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2444_, lean_object* v_k_2445_, lean_object* v_v_2446_, lean_object* v_t_2447_, lean_object* v_hl_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2445_, v_v_2446_, v_t_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2450_, lean_object* v_stx_2451_){
_start:
{
uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = 0;
lean_inc(v_pos_2450_);
v___x_2453_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2453_, 0, v_pos_2450_);
lean_ctor_set(v___x_2453_, 1, v_pos_2450_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*2, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_setInfo(v___x_2453_, v_stx_2451_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
v___x_2458_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2456_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2459_, v_stx_2455_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2468_, v_a_2469_);
lean_dec_ref(v_a_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2472_, v_a_2473_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2492_, lean_object* v_e_2493_, uint8_t v_isBinder_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_lctx_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_lctx_2497_ = lean_ctor_get(v_a_2495_, 2);
v___x_2498_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v_stx_2492_);
v___x_2500_ = lean_box(0);
v___x_2501_ = 0;
lean_inc_ref(v_lctx_2497_);
v___x_2502_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2502_, 0, v___x_2499_);
lean_ctor_set(v___x_2502_, 1, v_lctx_2497_);
lean_ctor_set(v___x_2502_, 2, v___x_2500_);
lean_ctor_set(v___x_2502_, 3, v_e_2493_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*4, v_isBinder_2494_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*4 + 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2504_, lean_object* v_e_2505_, lean_object* v_isBinder_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
uint8_t v_isBinder_boxed_2509_; lean_object* v_res_2510_; 
v_isBinder_boxed_2509_ = lean_unbox(v_isBinder_2506_);
v_res_2510_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2504_, v_e_2505_, v_isBinder_boxed_2509_, v_a_2507_);
lean_dec_ref(v_a_2507_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2511_, lean_object* v_e_2512_, uint8_t v_isBinder_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2511_, v_e_2512_, v_isBinder_2513_, v_a_2516_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2522_, lean_object* v_e_2523_, lean_object* v_isBinder_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
uint8_t v_isBinder_boxed_2532_; lean_object* v_res_2533_; 
v_isBinder_boxed_2532_ = lean_unbox(v_isBinder_2524_);
v_res_2533_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2522_, v_e_2523_, v_isBinder_boxed_2532_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2534_, lean_object* v_stx_2535_, lean_object* v_e_2536_, uint8_t v_isBinder_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2564_; 
v___x_2541_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2535_, v_e_2536_, v_isBinder_2537_, v_a_2539_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2564_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2564_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_steps_2548_; lean_object* v_infos_2549_; lean_object* v_holeIter_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2563_; 
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2542_);
v___x_2547_ = lean_st_ref_take(v_a_2538_);
v_steps_2548_ = lean_ctor_get(v___x_2547_, 0);
v_infos_2549_ = lean_ctor_get(v___x_2547_, 1);
v_holeIter_2550_ = lean_ctor_get(v___x_2547_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2552_ = v___x_2547_;
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_holeIter_2550_);
lean_inc(v_infos_2549_);
lean_inc(v_steps_2548_);
lean_dec(v___x_2547_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2534_, v___x_2546_, v_infos_2549_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_steps_2548_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_holeIter_2550_);
v___x_2557_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_st_ref_put(v_a_2538_, v___x_2557_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2554_);
v___x_2560_ = v___x_2544_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2554_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2565_, lean_object* v_stx_2566_, lean_object* v_e_2567_, lean_object* v_isBinder_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
uint8_t v_isBinder_boxed_2572_; lean_object* v_res_2573_; 
v_isBinder_boxed_2572_ = lean_unbox(v_isBinder_2568_);
v_res_2573_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2565_, v_stx_2566_, v_e_2567_, v_isBinder_boxed_2572_, v_a_2569_, v_a_2570_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2574_, lean_object* v_stx_2575_, lean_object* v_e_2576_, uint8_t v_isBinder_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2574_, v_stx_2575_, v_e_2576_, v_isBinder_2577_, v_a_2579_, v_a_2580_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2586_, lean_object* v_stx_2587_, lean_object* v_e_2588_, lean_object* v_isBinder_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_isBinder_boxed_2597_; lean_object* v_res_2598_; 
v_isBinder_boxed_2597_ = lean_unbox(v_isBinder_2589_);
v_res_2598_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2586_, v_stx_2587_, v_e_2588_, v_isBinder_boxed_2597_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2599_, lean_object* v_fieldName_2600_, lean_object* v_stx_2601_, lean_object* v_val_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_lctx_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_lctx_2605_ = lean_ctor_get(v_a_2603_, 2);
lean_inc_ref(v_lctx_2605_);
v___x_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2606_, 0, v_projName_2599_);
lean_ctor_set(v___x_2606_, 1, v_fieldName_2600_);
lean_ctor_set(v___x_2606_, 2, v_lctx_2605_);
lean_ctor_set(v___x_2606_, 3, v_val_2602_);
lean_ctor_set(v___x_2606_, 4, v_stx_2601_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2608_, lean_object* v_fieldName_2609_, lean_object* v_stx_2610_, lean_object* v_val_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2608_, v_fieldName_2609_, v_stx_2610_, v_val_2611_, v_a_2612_);
lean_dec_ref(v_a_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2615_, lean_object* v_fieldName_2616_, lean_object* v_stx_2617_, lean_object* v_val_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2615_, v_fieldName_2616_, v_stx_2617_, v_val_2618_, v_a_2621_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2627_, lean_object* v_fieldName_2628_, lean_object* v_stx_2629_, lean_object* v_val_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2627_, v_fieldName_2628_, v_stx_2629_, v_val_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2639_, lean_object* v_projName_2640_, lean_object* v_fieldName_2641_, lean_object* v_stx_2642_, lean_object* v_val_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___x_2647_; lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2670_; 
v___x_2647_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2640_, v_fieldName_2641_, v_stx_2642_, v_val_2643_, v_a_2645_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2670_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2670_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_steps_2654_; lean_object* v_infos_2655_; lean_object* v_holeIter_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2669_; 
v___x_2652_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_a_2648_);
v___x_2653_ = lean_st_ref_take(v_a_2644_);
v_steps_2654_ = lean_ctor_get(v___x_2653_, 0);
v_infos_2655_ = lean_ctor_get(v___x_2653_, 1);
v_holeIter_2656_ = lean_ctor_get(v___x_2653_, 2);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2658_ = v___x_2653_;
v_isShared_2659_ = v_isSharedCheck_2669_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_holeIter_2656_);
lean_inc(v_infos_2655_);
lean_inc(v_steps_2654_);
lean_dec(v___x_2653_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2669_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2639_, v___x_2652_, v_infos_2655_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2661_);
v___x_2663_ = v___x_2658_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_steps_2654_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_holeIter_2656_);
v___x_2663_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2664_ = lean_st_ref_put(v_a_2644_, v___x_2663_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2660_);
v___x_2666_ = v___x_2650_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2660_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2671_, lean_object* v_projName_2672_, lean_object* v_fieldName_2673_, lean_object* v_stx_2674_, lean_object* v_val_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2671_, v_projName_2672_, v_fieldName_2673_, v_stx_2674_, v_val_2675_, v_a_2676_, v_a_2677_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2680_, lean_object* v_projName_2681_, lean_object* v_fieldName_2682_, lean_object* v_stx_2683_, lean_object* v_val_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2680_, v_projName_2681_, v_fieldName_2682_, v_stx_2683_, v_val_2684_, v_a_2686_, v_a_2687_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2693_, lean_object* v_projName_2694_, lean_object* v_fieldName_2695_, lean_object* v_stx_2696_, lean_object* v_val_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2693_, v_projName_2694_, v_fieldName_2695_, v_stx_2696_, v_val_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_val_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2710_, v___y_2711_);
lean_dec_ref(v___y_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2714_, lean_object* v_stx_2715_, lean_object* v_e_2716_, uint8_t v_isBinder_2717_, lean_object* v_location_x3f_2718_, lean_object* v_docString_x3f_2719_, lean_object* v_mkDocString_x3f_2720_, uint8_t v_explicit_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2760_; 
v___x_2725_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2715_, v_e_2716_, v_isBinder_2717_, v_a_2723_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___y_2731_; 
if (lean_obj_tag(v_mkDocString_x3f_2720_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2719_) == 0)
{
v___y_2731_ = v_mkDocString_x3f_2720_;
goto v___jp_2730_;
}
else
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2759_; 
v_val_2751_ = lean_ctor_get(v_docString_x3f_2719_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_docString_x3f_2719_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2753_ = v_docString_x3f_2719_;
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v_docString_x3f_2719_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___f_2755_; lean_object* v___x_2757_; 
v___f_2755_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2755_, 0, v_val_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___f_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___f_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
v___y_2731_ = v___x_2757_;
goto v___jp_2730_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2719_);
v___y_2731_ = v_mkDocString_x3f_2720_;
goto v___jp_2730_;
}
v___jp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_steps_2735_; lean_object* v_infos_2736_; lean_object* v_holeIter_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2750_; 
v___x_2732_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2732_, 0, v_a_2726_);
lean_ctor_set(v___x_2732_, 1, v_location_x3f_2718_);
lean_ctor_set(v___x_2732_, 2, v___y_2731_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*3, v_explicit_2721_);
v___x_2733_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
v___x_2734_ = lean_st_ref_take(v_a_2722_);
v_steps_2735_ = lean_ctor_get(v___x_2734_, 0);
v_infos_2736_ = lean_ctor_get(v___x_2734_, 1);
v_holeIter_2737_ = lean_ctor_get(v___x_2734_, 2);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2739_ = v___x_2734_;
v_isShared_2740_ = v_isSharedCheck_2750_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_holeIter_2737_);
lean_inc(v_infos_2736_);
lean_inc(v_steps_2735_);
lean_dec(v___x_2734_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2750_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2714_, v___x_2733_, v_infos_2736_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 1, v___x_2742_);
v___x_2744_ = v___x_2739_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_steps_2735_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v_holeIter_2737_);
v___x_2744_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_st_ref_put(v_a_2722_, v___x_2744_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2741_);
v___x_2747_ = v___x_2728_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2741_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2761_, lean_object* v_stx_2762_, lean_object* v_e_2763_, lean_object* v_isBinder_2764_, lean_object* v_location_x3f_2765_, lean_object* v_docString_x3f_2766_, lean_object* v_mkDocString_x3f_2767_, lean_object* v_explicit_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
uint8_t v_isBinder_boxed_2772_; uint8_t v_explicit_boxed_2773_; lean_object* v_res_2774_; 
v_isBinder_boxed_2772_ = lean_unbox(v_isBinder_2764_);
v_explicit_boxed_2773_ = lean_unbox(v_explicit_2768_);
v_res_2774_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2761_, v_stx_2762_, v_e_2763_, v_isBinder_boxed_2772_, v_location_x3f_2765_, v_docString_x3f_2766_, v_mkDocString_x3f_2767_, v_explicit_boxed_2773_, v_a_2769_, v_a_2770_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2775_, lean_object* v_stx_2776_, lean_object* v_e_2777_, uint8_t v_isBinder_2778_, lean_object* v_location_x3f_2779_, lean_object* v_docString_x3f_2780_, lean_object* v_mkDocString_x3f_2781_, uint8_t v_explicit_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2775_, v_stx_2776_, v_e_2777_, v_isBinder_2778_, v_location_x3f_2779_, v_docString_x3f_2780_, v_mkDocString_x3f_2781_, v_explicit_2782_, v_a_2784_, v_a_2785_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2791_, lean_object* v_stx_2792_, lean_object* v_e_2793_, lean_object* v_isBinder_2794_, lean_object* v_location_x3f_2795_, lean_object* v_docString_x3f_2796_, lean_object* v_mkDocString_x3f_2797_, lean_object* v_explicit_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
uint8_t v_isBinder_boxed_2806_; uint8_t v_explicit_boxed_2807_; lean_object* v_res_2808_; 
v_isBinder_boxed_2806_ = lean_unbox(v_isBinder_2794_);
v_explicit_boxed_2807_ = lean_unbox(v_explicit_2798_);
v_res_2808_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2791_, v_stx_2792_, v_e_2793_, v_isBinder_boxed_2806_, v_location_x3f_2795_, v_docString_x3f_2796_, v_mkDocString_x3f_2797_, v_explicit_boxed_2807_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2809_, v_a_2810_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v_a_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_n(v_a_2815_, 2);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2810_);
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2810_);
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = 0;
v___x_2821_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2817_, v_a_2815_, v_a_2819_, v___x_2820_, v_a_2811_, v_a_2812_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v___x_2821_, 0);
lean_dec(v_unused_2829_);
v___x_2823_ = v___x_2821_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v___x_2821_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v_a_2815_);
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2815_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2815_);
v_a_2830_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2821_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2821_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2861_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2862_, lean_object* v_t_2863_){
_start:
{
if (lean_obj_tag(v_t_2863_) == 0)
{
lean_object* v_k_2864_; lean_object* v_l_2865_; lean_object* v_r_2866_; uint8_t v___x_2867_; 
v_k_2864_ = lean_ctor_get(v_t_2863_, 1);
v_l_2865_ = lean_ctor_get(v_t_2863_, 3);
v_r_2866_ = lean_ctor_get(v_t_2863_, 4);
v___x_2867_ = lean_nat_dec_lt(v_k_2862_, v_k_2864_);
if (v___x_2867_ == 0)
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_nat_dec_eq(v_k_2862_, v_k_2864_);
if (v___x_2868_ == 0)
{
v_t_2863_ = v_r_2866_;
goto _start;
}
else
{
return v___x_2868_;
}
}
else
{
v_t_2863_ = v_l_2865_;
goto _start;
}
}
else
{
uint8_t v___x_2871_; 
v___x_2871_ = 0;
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2872_, lean_object* v_t_2873_){
_start:
{
uint8_t v_res_2874_; lean_object* v_r_2875_; 
v_res_2874_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2872_, v_t_2873_);
lean_dec(v_t_2873_);
lean_dec(v_k_2872_);
v_r_2875_ = lean_box(v_res_2874_);
return v_r_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Syntax_getInfo_x3f(v_stx_2876_);
if (lean_obj_tag(v___x_2881_) == 1)
{
lean_object* v_val_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2900_; 
v_val_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2900_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_val_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2900_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
if (lean_obj_tag(v_val_2882_) == 1)
{
uint8_t v_canonical_2886_; 
v_canonical_2886_ = lean_ctor_get_uint8(v_val_2882_, sizeof(void*)*2);
if (v_canonical_2886_ == 0)
{
lean_object* v_pos_2887_; lean_object* v_endPos_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_pos_2887_ = lean_ctor_get(v_val_2882_, 0);
lean_inc(v_pos_2887_);
v_endPos_2888_ = lean_ctor_get(v_val_2882_, 1);
lean_inc(v_endPos_2888_);
lean_dec_ref_known(v_val_2882_, 2);
v___x_2889_ = lean_st_ref_get(v_a_2878_);
v___x_2890_ = lean_nat_dec_eq(v_pos_2887_, v_endPos_2888_);
lean_dec(v_endPos_2888_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v___x_2889_);
lean_dec(v_pos_2887_);
lean_del_object(v___x_2884_);
v___x_2891_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2891_;
}
else
{
lean_object* v_infos_2892_; uint8_t v___x_2893_; 
v_infos_2892_ = lean_ctor_get(v___x_2889_, 1);
lean_inc(v_infos_2892_);
lean_dec(v___x_2889_);
v___x_2893_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2887_, v_infos_2892_);
lean_dec(v_infos_2892_);
lean_dec(v_pos_2887_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_del_object(v___x_2884_);
v___x_2894_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2894_;
}
else
{
lean_object* v___x_2896_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set_tag(v___x_2884_, 0);
lean_ctor_set(v___x_2884_, 0, v_stx_2876_);
v___x_2896_ = v___x_2884_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_stx_2876_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v___x_2898_; 
lean_dec_ref_known(v_val_2882_, 2);
lean_del_object(v___x_2884_);
v___x_2898_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2898_;
}
}
else
{
lean_object* v___x_2899_; 
lean_del_object(v___x_2884_);
lean_dec(v_val_2882_);
v___x_2899_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2899_;
}
}
}
else
{
lean_object* v___x_2901_; 
lean_dec(v___x_2881_);
v___x_2901_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2926_, lean_object* v_k_2927_, lean_object* v_t_2928_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2927_, v_t_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2930_, lean_object* v_k_2931_, lean_object* v_t_2932_){
_start:
{
uint8_t v_res_2933_; lean_object* v_r_2934_; 
v_res_2933_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2930_, v_k_2931_, v_t_2932_);
lean_dec(v_t_2932_);
lean_dec(v_k_2931_);
v_r_2934_ = lean_box(v_res_2933_);
return v_r_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2943_; 
lean_inc(v_a_2941_);
lean_inc_ref(v_a_2940_);
lean_inc(v_a_2939_);
lean_inc_ref(v_a_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_a_2936_);
v___x_2943_ = lean_apply_7(v_d_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, lean_box(0));
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2944_, v_a_2936_, v_a_2937_, v_a_2938_);
return v___x_2945_;
}
else
{
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2963_; 
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
v___x_2963_ = lean_apply_7(v_d_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, lean_box(0));
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2964_, v_a_2956_, v_a_2957_, v_a_2958_);
return v___x_2965_;
}
else
{
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
return v_res_2974_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2975_, lean_object* v_suggestion_x27_2976_, lean_object* v_x_2977_){
_start:
{
if (lean_obj_tag(v_x_2977_) == 1)
{
lean_object* v_fvarId_2978_; lean_object* v___x_2979_; 
v_fvarId_2978_ = lean_ctor_get(v_x_2977_, 0);
lean_inc(v_fvarId_2978_);
lean_dec_ref_known(v_x_2977_, 1);
v___x_2979_ = lean_local_ctx_find(v_lctx_2975_, v_fvarId_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
uint8_t v___x_2980_; 
v___x_2980_ = 0;
return v___x_2980_;
}
else
{
lean_object* v_val_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_val_2981_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2982_ = l_Lean_LocalDecl_userName(v_val_2981_);
lean_dec(v_val_2981_);
v___x_2983_ = lean_name_eq(v___x_2982_, v_suggestion_x27_2976_);
lean_dec(v___x_2982_);
return v___x_2983_;
}
}
else
{
uint8_t v___x_2984_; 
lean_dec_ref(v_x_2977_);
lean_dec_ref(v_lctx_2975_);
v___x_2984_ = 0;
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2985_, lean_object* v_suggestion_x27_2986_, lean_object* v_x_2987_){
_start:
{
uint8_t v_res_2988_; lean_object* v_r_2989_; 
v_res_2988_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2985_, v_suggestion_x27_2986_, v_x_2987_);
lean_dec(v_suggestion_x27_2986_);
v_r_2989_ = lean_box(v_res_2988_);
return v_r_2989_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2990_, lean_object* v_lctx_2991_, lean_object* v_suggestion_x27_2992_){
_start:
{
lean_object* v___f_2993_; lean_object* v___x_2994_; 
v___f_2993_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2993_, 0, v_lctx_2991_);
lean_closure_set(v___f_2993_, 1, v_suggestion_x27_2992_);
v___x_2994_ = lean_find_expr(v___f_2993_, v_body_2990_);
lean_dec_ref(v___f_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
uint8_t v___x_2995_; 
v___x_2995_ = 0;
return v___x_2995_;
}
else
{
uint8_t v___x_2996_; 
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = 1;
return v___x_2996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2997_, lean_object* v_lctx_2998_, lean_object* v_suggestion_x27_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2997_, v_lctx_2998_, v_suggestion_x27_2999_);
lean_dec_ref(v_body_2997_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_toCold_3006_; lean_object* v_quotContext_3007_; lean_object* v_currMacroScope_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_toCold_3006_ = lean_ctor_get(v___y_3003_, 0);
lean_inc_ref(v_toCold_3006_);
lean_dec_ref(v___y_3003_);
v_quotContext_3007_ = lean_ctor_get(v_toCold_3006_, 8);
lean_inc(v_quotContext_3007_);
v_currMacroScope_3008_ = lean_ctor_get(v_toCold_3006_, 9);
lean_inc(v_currMacroScope_3008_);
lean_dec_ref(v_toCold_3006_);
v___x_3009_ = l_Lean_addMacroScope(v_quotContext_3007_, v_snd_3002_, v_currMacroScope_3008_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_3020_, lean_object* v_body_3021_, uint8_t v_preserveName_3022_, lean_object* v_avoid_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v_fst_3063_; lean_object* v_snd_3064_; uint8_t v___x_3070_; 
v___x_3070_ = l_Lean_Name_isAnonymous(v_suggestion_3020_);
if (v___x_3070_ == 0)
{
uint8_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = l_Lean_Name_hasMacroScopes(v_suggestion_3020_);
v___x_3072_ = l_Lean_Name_eraseMacroScopes(v_suggestion_3020_);
v_fst_3063_ = v___x_3071_;
v_snd_3064_ = v___x_3072_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3073_; 
v___x_3073_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3063_ = v___x_3070_;
v_snd_3064_ = v___x_3073_;
goto v___jp_3062_;
}
v___jp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = l_Lean_LocalContext_getUnusedName(v___y_3033_, v___y_3032_);
lean_dec(v___y_3032_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
v___jp_3036_:
{
if (v_preserveName_3022_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v___y_3038_);
v___x_3040_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3041_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3040_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3052_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3052_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3052_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_unbox(v_a_3042_);
lean_dec(v_a_3042_);
if (v___x_3046_ == 0)
{
lean_del_object(v___x_3044_);
v___y_3032_ = v___y_3037_;
v___y_3033_ = v___y_3039_;
goto v___jp_3031_;
}
else
{
uint8_t v___x_3047_; 
v___x_3047_ = l_Lean_NameSet_contains(v_avoid_3023_, v___y_3037_);
if (v___x_3047_ == 0)
{
uint8_t v___x_3048_; 
lean_inc(v___y_3037_);
lean_inc_ref(v___y_3039_);
v___x_3048_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_3021_, v___y_3039_, v___y_3037_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3050_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___y_3037_);
v___x_3050_ = v___x_3044_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___y_3037_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_del_object(v___x_3044_);
v___y_3032_ = v___y_3037_;
v___y_3033_ = v___y_3039_;
goto v___jp_3031_;
}
}
else
{
lean_del_object(v___x_3044_);
v___y_3032_ = v___y_3037_;
v___y_3033_ = v___y_3039_;
goto v___jp_3031_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v___y_3037_);
v_a_3053_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3041_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3041_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v___x_3061_; 
lean_dec(v___y_3037_);
v___x_3061_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3038_, v_a_3028_, v_a_3029_);
return v___x_3061_;
}
}
v___jp_3062_:
{
lean_object* v_lctx_3065_; uint8_t v___x_3066_; 
v_lctx_3065_ = lean_ctor_get(v_a_3026_, 2);
v___x_3066_ = l_Lean_LocalContext_usesUserName(v_lctx_3065_, v_snd_3064_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_snd_3064_);
return v___x_3067_;
}
else
{
lean_object* v___f_3068_; 
lean_inc(v_snd_3064_);
v___f_3068_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3068_, 0, v_snd_3064_);
if (v_preserveName_3022_ == 0)
{
v___y_3037_ = v_snd_3064_;
v___y_3038_ = v___f_3068_;
v___y_3039_ = v_lctx_3065_;
goto v___jp_3036_;
}
else
{
if (v_fst_3063_ == 0)
{
lean_object* v___x_3069_; 
lean_dec_ref(v___f_3068_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_snd_3064_);
return v___x_3069_;
}
else
{
v___y_3037_ = v_snd_3064_;
v___y_3038_ = v___f_3068_;
v___y_3039_ = v_lctx_3065_;
goto v___jp_3036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3074_, lean_object* v_body_3075_, lean_object* v_preserveName_3076_, lean_object* v_avoid_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v_preserveName_boxed_3085_; lean_object* v_res_3086_; 
v_preserveName_boxed_3085_ = lean_unbox(v_preserveName_3076_);
v_res_3086_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3074_, v_body_3075_, v_preserveName_boxed_3085_, v_avoid_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_avoid_3077_);
lean_dec_ref(v_body_3075_);
lean_dec(v_suggestion_3074_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v_holeIter_3090_; lean_object* v_curr_3091_; lean_object* v___x_3092_; lean_object* v_steps_3093_; lean_object* v_infos_3094_; lean_object* v_holeIter_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3105_; 
v___x_3089_ = lean_st_ref_get(v___y_3087_);
v_holeIter_3090_ = lean_ctor_get(v___x_3089_, 2);
lean_inc_ref(v_holeIter_3090_);
lean_dec(v___x_3089_);
v_curr_3091_ = lean_ctor_get(v_holeIter_3090_, 0);
lean_inc(v_curr_3091_);
lean_dec_ref(v_holeIter_3090_);
v___x_3092_ = lean_st_ref_take(v___y_3087_);
v_steps_3093_ = lean_ctor_get(v___x_3092_, 0);
v_infos_3094_ = lean_ctor_get(v___x_3092_, 1);
v_holeIter_3095_ = lean_ctor_get(v___x_3092_, 2);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3097_ = v___x_3092_;
v_isShared_3098_ = v_isSharedCheck_3105_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_holeIter_3095_);
lean_inc(v_infos_3094_);
lean_inc(v_steps_3093_);
lean_dec(v___x_3092_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3105_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 2, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_steps_3093_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_infos_3094_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_st_ref_put(v___y_3087_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_curr_3091_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3106_);
lean_dec(v___y_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3110_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3125_, lean_object* v_e_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v___x_3134_; lean_object* v_a_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3134_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3128_);
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_n(v_a_3135_, 2);
lean_dec_ref(v___x_3134_);
v___x_3136_ = l_Lean_mkIdent(v_n_3125_);
v___x_3137_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3135_, v___x_3136_);
v___x_3138_ = 0;
lean_inc(v___x_3137_);
v___x_3139_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3135_, v___x_3137_, v_e_3126_, v___x_3138_, v_a_3128_, v_a_3129_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3147_);
v___x_3141_ = v___x_3139_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_dec(v___x_3139_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3137_);
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3137_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v___x_3137_);
v_a_3148_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3139_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3139_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3156_, lean_object* v_e_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3156_, v_e_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3166_, lean_object* v_x_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
v___x_3175_ = lean_apply_8(v_d_3166_, v_x_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, lean_box(0));
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3176_, lean_object* v_x_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3176_, v_x_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v_b_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
v___x_3195_ = lean_apply_8(v_k_3186_, v_b_3189_, v___y_3187_, v___y_3188_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, lean_box(0));
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3196_, v___y_3197_, v___y_3198_, v_b_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3206_, uint8_t v_bi_3207_, lean_object* v_type_3208_, lean_object* v_k_3209_, uint8_t v_kind_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___f_3218_; lean_object* v___x_3219_; 
lean_inc(v___y_3212_);
lean_inc_ref(v___y_3211_);
v___f_3218_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3218_, 0, v_k_3209_);
lean_closure_set(v___f_3218_, 1, v___y_3211_);
lean_closure_set(v___f_3218_, 2, v___y_3212_);
v___x_3219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3206_, v_bi_3207_, v_type_3208_, v___f_3218_, v_kind_3210_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
if (lean_obj_tag(v___x_3219_) == 0)
{
return v___x_3219_;
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3228_, lean_object* v_bi_3229_, lean_object* v_type_3230_, lean_object* v_k_3231_, lean_object* v_kind_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v_bi_boxed_3240_; uint8_t v_kind_boxed_3241_; lean_object* v_res_3242_; 
v_bi_boxed_3240_ = lean_unbox(v_bi_3229_);
v_kind_boxed_3241_ = lean_unbox(v_kind_3232_);
v_res_3242_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3228_, v_bi_boxed_3240_, v_type_3230_, v_k_3231_, v_kind_boxed_3241_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3243_, lean_object* v_childIdx_3244_, lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_subExpr_3253_; lean_object* v_optionsPerPos_3254_; lean_object* v_currNamespace_3255_; lean_object* v_openDecls_3256_; uint8_t v_inPattern_3257_; lean_object* v_depth_3258_; lean_object* v_lctxInitIndices_3259_; lean_object* v_pos_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_subExpr_3253_ = lean_ctor_get(v___y_3246_, 3);
v_optionsPerPos_3254_ = lean_ctor_get(v___y_3246_, 0);
v_currNamespace_3255_ = lean_ctor_get(v___y_3246_, 1);
v_openDecls_3256_ = lean_ctor_get(v___y_3246_, 2);
v_inPattern_3257_ = lean_ctor_get_uint8(v___y_3246_, sizeof(void*)*6);
v_depth_3258_ = lean_ctor_get(v___y_3246_, 4);
v_lctxInitIndices_3259_ = lean_ctor_get(v___y_3246_, 5);
v_pos_3260_ = lean_ctor_get(v_subExpr_3253_, 1);
v___x_3261_ = l_Lean_SubExpr_Pos_push(v_pos_3260_, v_childIdx_3244_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_child_3243_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
lean_inc(v_lctxInitIndices_3259_);
lean_inc(v_depth_3258_);
lean_inc(v_openDecls_3256_);
lean_inc(v_currNamespace_3255_);
lean_inc(v_optionsPerPos_3254_);
v___x_3263_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3263_, 0, v_optionsPerPos_3254_);
lean_ctor_set(v___x_3263_, 1, v_currNamespace_3255_);
lean_ctor_set(v___x_3263_, 2, v_openDecls_3256_);
lean_ctor_set(v___x_3263_, 3, v___x_3262_);
lean_ctor_set(v___x_3263_, 4, v_depth_3258_);
lean_ctor_set(v___x_3263_, 5, v_lctxInitIndices_3259_);
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*6, v_inPattern_3257_);
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
v___x_3264_ = lean_apply_7(v_x_3245_, v___x_3263_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, lean_box(0));
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3265_, lean_object* v_childIdx_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3265_, v_childIdx_3266_, v_x_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3276_, lean_object* v_a_3277_, lean_object* v_x_3278_, lean_object* v_fvar_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3282_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc_ref(v_fvar_3279_);
v___x_3287_ = lean_apply_8(v_v_3276_, v_fvar_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, lean_box(0));
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = l_Lean_Expr_bindingBody_x21(v_a_3277_);
v___x_3290_ = lean_expr_instantiate1(v___x_3289_, v_fvar_3279_);
lean_dec_ref(v_fvar_3279_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = lean_unsigned_to_nat(1u);
v___x_3292_ = lean_apply_1(v_x_3278_, v_a_3288_);
v___x_3293_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3290_, v___x_3291_, v___x_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v_fvar_3279_);
lean_dec_ref(v_x_3278_);
v_a_3294_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3287_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3287_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3302_, lean_object* v_a_3303_, lean_object* v_x_3304_, lean_object* v_fvar_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3302_, v_a_3303_, v_x_3304_, v_fvar_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_a_3303_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3314_, lean_object* v_v_3315_, lean_object* v_x_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v___f_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3324_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3317_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc_n(v_a_3325_, 2);
lean_dec_ref(v___x_3324_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3326_, 0, v_v_3315_);
lean_closure_set(v___f_3326_, 1, v_a_3325_);
lean_closure_set(v___f_3326_, 2, v_x_3316_);
v___x_3327_ = l_Lean_Expr_binderInfo(v_a_3325_);
v___x_3328_ = l_Lean_Expr_bindingDomain_x21(v_a_3325_);
lean_dec(v_a_3325_);
v___x_3329_ = 0;
v___x_3330_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3314_, v___x_3327_, v___x_3328_, v___f_3326_, v___x_3329_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3331_, lean_object* v_v_3332_, lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3331_, v_v_3332_, v_x_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3342_, uint8_t v_preserveName_3343_, lean_object* v_avoid_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v_a_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3352_, 0, v_d_3342_);
v___x_3353_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3345_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___x_3353_);
v___x_3355_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3345_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = l_Lean_Expr_bindingName_x21(v_a_3354_);
lean_dec(v_a_3354_);
v___x_3358_ = l_Lean_Expr_bindingBody_x21(v_a_3356_);
lean_dec(v_a_3356_);
v___x_3359_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3357_, v___x_3358_, v_preserveName_3343_, v_avoid_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec_ref(v___x_3358_);
lean_dec(v___x_3357_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_n(v_a_3360_, 2);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3361_, 0, v_a_3360_);
v___x_3362_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3360_, v___x_3361_, v___f_3352_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
return v___x_3362_;
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v___f_3352_);
v_a_3363_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3359_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3359_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3371_, lean_object* v_preserveName_3372_, lean_object* v_avoid_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
uint8_t v_preserveName_boxed_3381_; lean_object* v_res_3382_; 
v_preserveName_boxed_3381_ = lean_unbox(v_preserveName_3372_);
v_res_3382_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3371_, v_preserveName_boxed_3381_, v_avoid_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_avoid_3373_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3383_, lean_object* v_d_3384_, uint8_t v_preserveName_3385_, lean_object* v_avoid_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3384_, v_preserveName_3385_, v_avoid_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3395_, lean_object* v_d_3396_, lean_object* v_preserveName_3397_, lean_object* v_avoid_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
uint8_t v_preserveName_boxed_3406_; lean_object* v_res_3407_; 
v_preserveName_boxed_3406_ = lean_unbox(v_preserveName_3397_);
v_res_3407_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3395_, v_d_3396_, v_preserveName_boxed_3406_, v_avoid_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_avoid_3398_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3408_, lean_object* v_child_3409_, lean_object* v_childIdx_3410_, lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3409_, v_childIdx_3410_, v_x_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3420_, lean_object* v_child_3421_, lean_object* v_childIdx_3422_, lean_object* v_x_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3420_, v_child_3421_, v_childIdx_3422_, v_x_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3432_, lean_object* v_name_3433_, uint8_t v_bi_3434_, lean_object* v_type_3435_, lean_object* v_k_3436_, uint8_t v_kind_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3433_, v_bi_3434_, v_type_3435_, v_k_3436_, v_kind_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3446_, lean_object* v_name_3447_, lean_object* v_bi_3448_, lean_object* v_type_3449_, lean_object* v_k_3450_, lean_object* v_kind_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v_bi_boxed_3459_; uint8_t v_kind_boxed_3460_; lean_object* v_res_3461_; 
v_bi_boxed_3459_ = lean_unbox(v_bi_3448_);
v_kind_boxed_3460_ = lean_unbox(v_kind_3451_);
v_res_3461_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3446_, v_name_3447_, v_bi_boxed_3459_, v_type_3449_, v_k_3450_, v_kind_boxed_3460_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3462_, lean_object* v_00_u03b2_3463_, lean_object* v_n_3464_, lean_object* v_v_3465_, lean_object* v_x_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3464_, v_v_3465_, v_x_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3475_, lean_object* v_00_u03b2_3476_, lean_object* v_n_3477_, lean_object* v_v_3478_, lean_object* v_x_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3475_, v_00_u03b2_3476_, v_n_3477_, v_v_3478_, v_x_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(lean_object* v_x_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_obj_tag_nat(v_x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl___boxed(lean_object* v_x_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___impl(v_x_3490_);
lean_dec(v_x_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3492_, lean_object* v_k_3493_){
_start:
{
if (lean_obj_tag(v_t_3492_) == 3)
{
lean_object* v_s_3494_; lean_object* v___x_3495_; 
v_s_3494_ = lean_ctor_get(v_t_3492_, 0);
lean_inc_ref(v_s_3494_);
lean_dec_ref_known(v_t_3492_, 1);
v___x_3495_ = lean_apply_1(v_k_3493_, v_s_3494_);
return v___x_3495_;
}
else
{
lean_dec(v_t_3492_);
return v_k_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3496_, lean_object* v_ctorIdx_3497_, lean_object* v_t_3498_, lean_object* v_h_3499_, lean_object* v_k_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3498_, v_k_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3502_, lean_object* v_ctorIdx_3503_, lean_object* v_t_3504_, lean_object* v_h_3505_, lean_object* v_k_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3502_, v_ctorIdx_3503_, v_t_3504_, v_h_3505_, v_k_3506_);
lean_dec(v_ctorIdx_3503_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3508_, lean_object* v_deep_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3508_, v_deep_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3511_, lean_object* v_t_3512_, lean_object* v_h_3513_, lean_object* v_deep_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3512_, v_deep_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3516_, lean_object* v_proof_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3516_, v_proof_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3519_, lean_object* v_t_3520_, lean_object* v_h_3521_, lean_object* v_proof_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3520_, v_proof_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3524_, lean_object* v_maxSteps_3525_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3524_, v_maxSteps_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3527_, lean_object* v_t_3528_, lean_object* v_h_3529_, lean_object* v_maxSteps_3530_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3528_, v_maxSteps_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3532_, lean_object* v_string_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3532_, v_string_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3535_, lean_object* v_t_3536_, lean_object* v_h_3537_, lean_object* v_string_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3536_, v_string_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3543_){
_start:
{
switch(lean_obj_tag(v_x_3543_))
{
case 0:
{
lean_object* v___x_3544_; 
v___x_3544_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3544_;
}
case 1:
{
lean_object* v___x_3545_; 
v___x_3545_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3545_;
}
case 2:
{
lean_object* v___x_3546_; 
v___x_3546_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3546_;
}
default: 
{
lean_object* v_s_3547_; 
v_s_3547_ = lean_ctor_get(v_x_3543_, 0);
lean_inc_ref(v_s_3547_);
return v_s_3547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3548_);
lean_dec(v_x_3548_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3550_, lean_object* v_stx_3551_, lean_object* v_e_3552_, lean_object* v_reason_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
uint8_t v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3557_ = 0;
v___x_3558_ = lean_box(0);
v___x_3559_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3553_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
v___x_3561_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3550_, v_stx_3551_, v_e_3552_, v___x_3557_, v___x_3558_, v___x_3560_, v___x_3558_, v___x_3557_, v_a_3554_, v_a_3555_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3562_, lean_object* v_stx_3563_, lean_object* v_e_3564_, lean_object* v_reason_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3562_, v_stx_3563_, v_e_3564_, v_reason_3565_, v_a_3566_, v_a_3567_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec(v_reason_3565_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3570_, lean_object* v_stx_3571_, lean_object* v_e_3572_, lean_object* v_reason_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3570_, v_stx_3571_, v_e_3572_, v_reason_3573_, v_a_3575_, v_a_3576_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3582_, lean_object* v_stx_3583_, lean_object* v_e_3584_, lean_object* v_reason_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3582_, v_stx_3583_, v_e_3584_, v_reason_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_reason_3585_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3594_, lean_object* v_ctx_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_optionsPerPos_3602_; lean_object* v_currNamespace_3603_; lean_object* v_openDecls_3604_; uint8_t v_inPattern_3605_; lean_object* v_subExpr_3606_; lean_object* v_depth_3607_; lean_object* v_lctxInitIndices_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_optionsPerPos_3602_ = lean_ctor_get(v_ctx_3595_, 0);
v_currNamespace_3603_ = lean_ctor_get(v_ctx_3595_, 1);
v_openDecls_3604_ = lean_ctor_get(v_ctx_3595_, 2);
v_inPattern_3605_ = lean_ctor_get_uint8(v_ctx_3595_, sizeof(void*)*6);
v_subExpr_3606_ = lean_ctor_get(v_ctx_3595_, 3);
v_depth_3607_ = lean_ctor_get(v_ctx_3595_, 4);
v_lctxInitIndices_3608_ = lean_ctor_get(v_ctx_3595_, 5);
v___x_3609_ = lean_unsigned_to_nat(1u);
v___x_3610_ = lean_nat_add(v_depth_3607_, v___x_3609_);
lean_inc(v_lctxInitIndices_3608_);
lean_inc_ref(v_subExpr_3606_);
lean_inc(v_openDecls_3604_);
lean_inc(v_currNamespace_3603_);
lean_inc(v_optionsPerPos_3602_);
v___x_3611_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3611_, 0, v_optionsPerPos_3602_);
lean_ctor_set(v___x_3611_, 1, v_currNamespace_3603_);
lean_ctor_set(v___x_3611_, 2, v_openDecls_3604_);
lean_ctor_set(v___x_3611_, 3, v_subExpr_3606_);
lean_ctor_set(v___x_3611_, 4, v___x_3610_);
lean_ctor_set(v___x_3611_, 5, v_lctxInitIndices_3608_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*6, v_inPattern_3605_);
lean_inc(v_a_3600_);
lean_inc_ref(v_a_3599_);
lean_inc(v_a_3598_);
lean_inc_ref(v_a_3597_);
lean_inc(v_a_3596_);
v___x_3612_ = lean_apply_7(v_act_3594_, v___x_3611_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, lean_box(0));
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3613_, lean_object* v_ctx_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3613_, v_ctx_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_ctx_3614_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3622_, lean_object* v_act_3623_, lean_object* v_ctx_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3623_, v_ctx_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3632_, lean_object* v_act_3633_, lean_object* v_ctx_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3632_, v_act_3633_, v_ctx_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_ctx_3634_);
return v_res_3641_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3642_, lean_object* v_e_3643_){
_start:
{
lean_object* v___y_3645_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = lean_unsigned_to_nat(254u);
v___x_3650_ = lean_nat_dec_le(v___x_3649_, v_threshold_3642_);
if (v___x_3650_ == 0)
{
v___y_3645_ = v_threshold_3642_;
goto v___jp_3644_;
}
else
{
v___y_3645_ = v___x_3649_;
goto v___jp_3644_;
}
v___jp_3644_:
{
uint32_t v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = l_Lean_Expr_approxDepth(v_e_3643_);
v___x_3647_ = lean_uint32_to_nat(v___x_3646_);
v___x_3648_ = lean_nat_dec_le(v___x_3647_, v___y_3645_);
lean_dec(v___x_3647_);
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3651_, lean_object* v_e_3652_){
_start:
{
uint8_t v_res_3653_; lean_object* v_r_3654_; 
v_res_3653_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3651_, v_e_3652_);
lean_dec_ref(v_e_3652_);
lean_dec(v_threshold_3651_);
v_r_3654_ = lean_box(v_res_3653_);
return v_r_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
uint8_t v___x_3665_; 
v___x_3665_ = l_Lean_Expr_isAtomic(v_e_3657_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3667_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3666_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3710_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3710_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3710_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v___x_3672_; 
v___x_3672_ = lean_unbox(v_a_3668_);
if (v___x_3672_ == 0)
{
lean_object* v_depth_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_del_object(v___x_3670_);
v_depth_3673_ = lean_ctor_get(v_a_3658_, 4);
v___x_3674_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3675_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3674_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3697_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3697_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3697_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3680_ = lean_nat_sub(v_depth_3673_, v_a_3676_);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = lean_nat_dec_lt(v___x_3681_, v___x_3680_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3684_; 
lean_dec(v___x_3680_);
lean_dec(v_a_3676_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_a_3668_);
v___x_3684_ = v___x_3678_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3668_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3686_ = lean_unsigned_to_nat(2u);
v___x_3687_ = lean_nat_shiftr(v_a_3676_, v___x_3686_);
lean_dec(v_a_3676_);
v___x_3688_ = lean_nat_sub(v___x_3687_, v___x_3680_);
lean_dec(v___x_3680_);
lean_dec(v___x_3687_);
v___x_3689_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3688_, v_e_3657_);
lean_dec(v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
lean_dec(v_a_3668_);
v___x_3690_ = lean_box(v___x_3682_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3690_);
v___x_3692_ = v___x_3678_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
else
{
lean_object* v___x_3695_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_a_3668_);
v___x_3695_ = v___x_3678_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3668_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_a_3668_);
v_a_3698_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3675_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3675_);
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
lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_dec(v_a_3668_);
v___x_3706_ = lean_box(v___x_3665_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3706_);
v___x_3708_ = v___x_3670_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
else
{
return v___x_3667_;
}
}
else
{
uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = 0;
v___x_3712_ = lean_box(v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_e_3714_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
uint8_t v___x_3733_; 
v___x_3733_ = l_Lean_Expr_isAtomic(v_e_3725_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3735_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3734_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3781_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3738_ = v___x_3735_;
v_isShared_3739_ = v_isSharedCheck_3781_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3781_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_unbox(v_a_3736_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_del_object(v___x_3738_);
lean_inc_ref(v_e_3725_);
v___x_3741_ = l_Lean_Meta_isProof(v_e_3725_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; uint8_t v___x_3743_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v___x_3743_ = lean_unbox(v_a_3742_);
if (v___x_3743_ == 0)
{
lean_dec(v_a_3736_);
lean_dec_ref(v_e_3725_);
return v___x_3741_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_inc(v_a_3742_);
lean_dec_ref_known(v___x_3741_, 1);
v___x_3744_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3745_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3744_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3757_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3757_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3757_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
uint8_t v___x_3750_; 
v___x_3750_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3746_, v_e_3725_);
lean_dec_ref(v_e_3725_);
lean_dec(v_a_3746_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3752_; 
lean_dec(v_a_3736_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v_a_3742_);
v___x_3752_ = v___x_3748_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3742_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
else
{
lean_object* v___x_3755_; 
lean_dec(v_a_3742_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v_a_3736_);
v___x_3755_ = v___x_3748_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3736_);
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
lean_dec(v_a_3742_);
lean_dec(v_a_3736_);
lean_dec_ref(v_e_3725_);
v_a_3758_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3745_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3745_);
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
}
else
{
lean_object* v_a_3766_; uint8_t v___x_3767_; 
lean_dec_ref(v_e_3725_);
v_a_3766_ = lean_ctor_get(v___x_3741_, 0);
v___x_3767_ = l_Lean_Exception_isInterrupt(v_a_3766_);
if (v___x_3767_ == 0)
{
uint8_t v___x_3768_; 
lean_inc(v_a_3766_);
v___x_3768_ = l_Lean_Exception_isRuntime(v_a_3766_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3776_);
v___x_3770_ = v___x_3741_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_dec(v___x_3741_);
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
lean_ctor_set(v___x_3770_, 0, v_a_3736_);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3736_);
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
lean_dec(v_a_3736_);
return v___x_3741_;
}
}
else
{
lean_dec(v_a_3736_);
return v___x_3741_;
}
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_dec(v_a_3736_);
lean_dec_ref(v_e_3725_);
v___x_3777_ = lean_box(v___x_3733_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3777_);
v___x_3779_ = v___x_3738_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_dec_ref(v_e_3725_);
return v___x_3735_;
}
}
else
{
uint8_t v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec_ref(v_e_3725_);
v___x_3782_ = 0;
v___x_3783_ = lean_box(v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_ref_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_ref_3808_ = lean_ctor_get(v_a_3806_, 2);
v___x_3809_ = 0;
v___x_3810_ = l_Lean_SourceInfo_fromRef(v_ref_3808_, v___x_3809_);
v___x_3811_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3812_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3810_);
v___x_3813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3810_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = l_Lean_Syntax_node1(v___x_3810_, v___x_3811_, v___x_3813_);
v___x_3815_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3814_, v_a_3803_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3817_; lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc_n(v_a_3816_, 2);
lean_dec_ref_known(v___x_3815_, 1);
v___x_3817_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3803_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3817_);
v___x_3819_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3803_);
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3818_, v_a_3816_, v_a_3820_, v_reason_3802_, v_a_3804_, v_a_3805_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v___x_3821_, 0);
lean_dec(v_unused_3829_);
v___x_3823_ = v___x_3821_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v___x_3821_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v_a_3816_);
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3816_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_a_3816_);
v_a_3830_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3821_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3821_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec_ref(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_reason_3838_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3850_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_reason_3854_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3871_;
}
else
{
lean_object* v_head_3872_; lean_object* v_tail_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_head_3872_ = lean_ctor_get(v_x_3863_, 0);
lean_inc(v_head_3872_);
v_tail_3873_ = lean_ctor_get(v_x_3863_, 1);
lean_inc(v_tail_3873_);
lean_dec_ref_known(v_x_3863_, 2);
v___x_3874_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
lean_inc(v___y_3867_);
lean_inc_ref(v___y_3866_);
lean_inc(v___y_3865_);
lean_inc_ref(v___y_3864_);
v___x_3875_ = lean_apply_7(v_head_3872_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, lean_box(0));
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_dec(v_tail_3873_);
return v___x_3875_;
}
else
{
lean_object* v_a_3876_; uint8_t v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
v___x_3877_ = l_Lean_Exception_isInterrupt(v_a_3876_);
if (v___x_3877_ == 0)
{
uint8_t v___x_3878_; 
lean_inc(v_a_3876_);
v___x_3878_ = l_Lean_Exception_isRuntime(v_a_3876_);
if (v___x_3878_ == 0)
{
if (lean_obj_tag(v_a_3876_) == 0)
{
lean_dec_ref_known(v_a_3876_, 2);
lean_dec(v_tail_3873_);
return v___x_3875_;
}
else
{
lean_object* v_id_3879_; uint8_t v___x_3880_; 
v_id_3879_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_id_3879_);
lean_dec_ref_known(v_a_3876_, 2);
v___x_3880_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3874_, v_id_3879_);
lean_dec(v_id_3879_);
if (v___x_3880_ == 0)
{
lean_dec(v_tail_3873_);
return v___x_3875_;
}
else
{
lean_dec_ref_known(v___x_3875_, 1);
v_x_3863_ = v_tail_3873_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3876_);
lean_dec(v_tail_3873_);
return v___x_3875_;
}
}
else
{
lean_dec(v_a_3876_);
lean_dec(v_tail_3873_);
return v___x_3875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
if (lean_obj_tag(v_x_3891_) == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3899_;
}
else
{
lean_object* v___x_3900_; lean_object* v___y_3902_; lean_object* v_a_3903_; lean_object* v___x_3912_; lean_object* v_env_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3900_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3912_ = lean_st_ref_get(v_a_3897_);
v_env_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc_ref(v_env_3913_);
lean_dec(v___x_3912_);
v___x_3914_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3915_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3914_, v_env_3913_, v_x_3891_);
v___x_3916_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3915_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3917_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_dec(v_x_3891_);
return v___x_3918_;
}
else
{
lean_object* v_a_3919_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
v___y_3902_ = v___x_3918_;
v_a_3903_ = v_a_3919_;
goto v___jp_3901_;
}
}
else
{
lean_object* v_a_3920_; 
v_a_3920_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3920_);
v___y_3902_ = v___x_3916_;
v_a_3903_ = v_a_3920_;
goto v___jp_3901_;
}
v___jp_3901_:
{
uint8_t v___x_3904_; 
v___x_3904_ = l_Lean_Exception_isInterrupt(v_a_3903_);
if (v___x_3904_ == 0)
{
uint8_t v___x_3905_; 
lean_inc_ref(v_a_3903_);
v___x_3905_ = l_Lean_Exception_isRuntime(v_a_3903_);
if (v___x_3905_ == 0)
{
if (lean_obj_tag(v_a_3903_) == 0)
{
lean_dec_ref_known(v_a_3903_, 2);
lean_dec(v_x_3891_);
return v___y_3902_;
}
else
{
lean_object* v_id_3906_; uint8_t v___x_3907_; 
v_id_3906_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_id_3906_);
lean_dec_ref_known(v_a_3903_, 2);
v___x_3907_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3900_, v_id_3906_);
lean_dec(v_id_3906_);
if (v___x_3907_ == 0)
{
lean_dec(v_x_3891_);
return v___y_3902_;
}
else
{
uint8_t v___x_3908_; 
lean_dec_ref(v___y_3902_);
v___x_3908_ = l_Lean_Name_isAtomic(v_x_3891_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Name_getRoot(v_x_3891_);
lean_dec(v_x_3891_);
v_x_3891_ = v___x_3909_;
goto _start;
}
else
{
lean_object* v___x_3911_; 
lean_dec(v_x_3891_);
v___x_3911_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3911_;
}
}
}
}
else
{
lean_dec_ref(v_a_3903_);
lean_dec(v_x_3891_);
return v___y_3902_;
}
}
else
{
lean_dec_ref(v_a_3903_);
lean_dec(v_x_3891_);
return v___y_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___x_3936_; lean_object* v_env_3937_; uint8_t v___x_3938_; lean_object* v_env_3939_; lean_object* v___x_3940_; lean_object* v_toCold_3941_; lean_object* v_mctx_3942_; lean_object* v_lctx_3943_; lean_object* v_options_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3936_ = lean_st_ref_get(v___y_3934_);
v_env_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc_ref(v_env_3937_);
lean_dec(v___x_3936_);
v___x_3938_ = 0;
v_env_3939_ = l_Lean_Environment_setRecordingDeps(v_env_3937_, v___x_3938_);
v___x_3940_ = lean_st_ref_get(v___y_3932_);
v_toCold_3941_ = lean_ctor_get(v___y_3933_, 0);
v_mctx_3942_ = lean_ctor_get(v___x_3940_, 0);
lean_inc_ref(v_mctx_3942_);
lean_dec(v___x_3940_);
v_lctx_3943_ = lean_ctor_get(v___y_3931_, 2);
v_options_3944_ = lean_ctor_get(v_toCold_3941_, 2);
lean_inc_ref(v_options_3944_);
lean_inc_ref(v_lctx_3943_);
v___x_3945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3945_, 0, v_env_3939_);
lean_ctor_set(v___x_3945_, 1, v_mctx_3942_);
lean_ctor_set(v___x_3945_, 2, v_lctx_3943_);
lean_ctor_set(v___x_3945_, 3, v_options_3944_);
v___x_3946_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v_msgData_3930_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_ref_3961_; lean_object* v___x_3962_; lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3971_; 
v_ref_3961_ = lean_ctor_get(v___y_3958_, 2);
v___x_3962_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
lean_inc(v_ref_3961_);
v___x_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3967_, 0, v_ref_3961_);
lean_ctor_set(v___x_3967_, 1, v_a_3963_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 1);
lean_ctor_set(v___x_3965_, 0, v___x_3967_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3978_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3981_ = l_Lean_stringToMessageData(v___x_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_inc(v_a_3982_);
v___x_3991_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_dec(v_a_3982_);
return v___x_3991_;
}
else
{
lean_object* v_a_3992_; uint8_t v___x_3993_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
v___x_3993_ = l_Lean_Exception_isInterrupt(v_a_3992_);
if (v___x_3993_ == 0)
{
uint8_t v___x_3994_; 
lean_inc(v_a_3992_);
v___x_3994_ = l_Lean_Exception_isRuntime(v_a_3992_);
if (v___x_3994_ == 0)
{
if (lean_obj_tag(v_a_3992_) == 0)
{
lean_dec_ref_known(v_a_3992_, 2);
lean_dec(v_a_3982_);
return v___x_3991_;
}
else
{
lean_object* v_id_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4008_; 
v_id_3995_ = lean_ctor_get(v_a_3992_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_a_3992_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v_a_3992_, 1);
lean_dec(v_unused_4009_);
v___x_3997_ = v_a_3992_;
v_isShared_3998_ = v_isSharedCheck_4008_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_id_3995_);
lean_dec(v_a_3992_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4008_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3990_, v_id_3995_);
lean_dec(v_id_3995_);
if (v___x_3999_ == 0)
{
lean_del_object(v___x_3997_);
lean_dec(v_a_3982_);
return v___x_3991_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_dec_ref_known(v___x_3991_, 1);
v___x_4000_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_4001_ = l_Lean_MessageData_ofName(v_a_3982_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 7);
lean_ctor_set(v___x_3997_, 1, v___x_4001_);
lean_ctor_set(v___x_3997_, 0, v___x_4000_);
v___x_4003_ = v___x_3997_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4000_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_4005_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
return v___x_4006_;
}
}
}
}
}
else
{
lean_dec(v_a_3992_);
lean_dec(v_a_3982_);
return v___x_3991_;
}
}
else
{
lean_dec(v_a_3992_);
lean_dec(v_a_3982_);
return v___x_3991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; lean_object* v_a_4028_; lean_object* v___x_4029_; 
v___x_4027_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4020_);
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref(v___x_4027_);
lean_inc(v___y_4025_);
lean_inc_ref(v___y_4024_);
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
v___x_4029_ = lean_infer_type(v_a_4028_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4032_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4030_, v___x_4031_, v_x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
return v___x_4032_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_x_4019_);
v_a_4033_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4029_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4029_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
return v_res_4049_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4070_ = l_String_toRawSubstring_x27(v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
lean_dec(v_a_4116_);
lean_dec_ref(v_a_4115_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
lean_dec_ref(v_a_4111_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_4127_ = l_Lean_Core_checkSystem(v___x_4126_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec_ref_known(v___x_4127_, 1);
v___x_4128_ = lean_st_ref_get(v_a_4120_);
v___x_4129_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4130_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4129_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v_steps_4132_; uint8_t v___x_4133_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v_steps_4132_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_steps_4132_);
lean_dec(v___x_4128_);
v___x_4133_ = lean_nat_dec_le(v_a_4131_, v_steps_4132_);
lean_dec(v_steps_4132_);
lean_dec(v_a_4131_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v_steps_4135_; lean_object* v_infos_4136_; lean_object* v_holeIter_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4316_; 
v___x_4134_ = lean_st_ref_take(v_a_4120_);
v_steps_4135_ = lean_ctor_get(v___x_4134_, 0);
v_infos_4136_ = lean_ctor_get(v___x_4134_, 1);
v_holeIter_4137_ = lean_ctor_get(v___x_4134_, 2);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4139_ = v___x_4134_;
v_isShared_4140_ = v_isSharedCheck_4316_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_holeIter_4137_);
lean_inc(v_infos_4136_);
lean_inc(v_steps_4135_);
lean_dec(v___x_4134_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4316_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = lean_nat_add(v_steps_4135_, v___x_4141_);
lean_dec(v_steps_4135_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4142_);
v___x_4144_ = v___x_4139_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_infos_4136_);
lean_ctor_set(v_reuseFailAlloc_4315_, 2, v_holeIter_4137_);
v___x_4144_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_st_ref_put(v_a_4120_, v___x_4144_);
v___x_4146_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4119_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4148_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
v___x_4148_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4147_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; uint8_t v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = lean_unbox(v_a_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; 
lean_inc(v_a_4147_);
v___x_4151_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4147_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; uint8_t v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = lean_unbox(v_a_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec(v_a_4149_);
v___x_4154_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4156_, 0, v_a_4155_);
v___x_4157_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4156_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__1));
v___x_4160_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4159_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4221_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4221_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4221_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
uint8_t v___x_4165_; 
v___x_4165_ = lean_unbox(v_a_4161_);
lean_dec(v_a_4161_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4167_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v_a_4158_);
v___x_4167_ = v___x_4163_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4158_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_del_object(v___x_4163_);
v___x_4169_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4170_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4169_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4212_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4212_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4212_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
uint8_t v___x_4175_; 
v___x_4175_ = lean_unbox(v_a_4171_);
lean_dec(v_a_4171_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4177_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_a_4158_);
v___x_4177_ = v___x_4173_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4158_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
uint8_t v___x_4179_; 
v___x_4179_ = l_Lean_Expr_isMData(v_a_4147_);
lean_dec(v_a_4147_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_del_object(v___x_4173_);
v___x_4180_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4181_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4180_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_toCold_4182_; lean_object* v_a_4183_; lean_object* v_ref_4184_; lean_object* v_quotContext_4185_; lean_object* v_currMacroScope_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_toCold_4182_ = lean_ctor_get(v_a_4123_, 0);
v_a_4183_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4181_, 1);
v_ref_4184_ = lean_ctor_get(v_a_4123_, 2);
v_quotContext_4185_ = lean_ctor_get(v_toCold_4182_, 8);
v_currMacroScope_4186_ = lean_ctor_get(v_toCold_4182_, 9);
v___x_4187_ = lean_unbox(v_a_4152_);
lean_dec(v_a_4152_);
v___x_4188_ = l_Lean_SourceInfo_fromRef(v_ref_4184_, v___x_4187_);
v___x_4189_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4190_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__6));
v___x_4191_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
lean_inc_n(v___x_4188_, 7);
v___x_4192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4188_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__9));
v___x_4194_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__10, &l_Lean_PrettyPrinter_Delaborator_delab___closed__10_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10);
v___x_4195_ = lean_box(0);
lean_inc(v_currMacroScope_4186_);
lean_inc(v_quotContext_4185_);
v___x_4196_ = l_Lean_addMacroScope(v_quotContext_4185_, v___x_4195_, v_currMacroScope_4186_);
v___x_4197_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4188_);
lean_ctor_set(v___x_4198_, 1, v___x_4194_);
lean_ctor_set(v___x_4198_, 2, v___x_4196_);
lean_ctor_set(v___x_4198_, 3, v___x_4197_);
v___x_4199_ = l_Lean_Syntax_node1(v___x_4188_, v___x_4193_, v___x_4198_);
v___x_4200_ = l_Lean_Syntax_node2(v___x_4188_, v___x_4190_, v___x_4192_, v___x_4199_);
v___x_4201_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4188_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_4204_ = l_Lean_Syntax_node1(v___x_4188_, v___x_4203_, v_a_4183_);
v___x_4205_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4188_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = l_Lean_Syntax_node5(v___x_4188_, v___x_4189_, v___x_4200_, v_a_4158_, v___x_4202_, v___x_4204_, v___x_4206_);
v___x_4208_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4207_, v_a_4119_);
return v___x_4208_;
}
else
{
lean_dec(v_a_4158_);
lean_dec(v_a_4152_);
return v___x_4181_;
}
}
else
{
lean_object* v___x_4210_; 
lean_dec(v_a_4152_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_a_4158_);
v___x_4210_ = v___x_4173_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4158_);
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
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v_a_4158_);
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
v_a_4213_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4170_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4170_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_a_4158_);
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
v_a_4222_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4160_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4160_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
return v___x_4157_;
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
v_a_4230_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4154_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4154_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
v___x_4238_ = lean_box(1);
v___x_4239_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4238_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4123_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
v___x_4241_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4242_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4241_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4280_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4280_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_unbox(v_a_4243_);
lean_dec(v_a_4243_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4249_; 
lean_dec(v_a_4149_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v_a_4240_);
v___x_4249_ = v___x_4245_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4240_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
else
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_del_object(v___x_4245_);
v___x_4251_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4252_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4251_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_toCold_4253_; lean_object* v_a_4254_; lean_object* v_ref_4255_; lean_object* v_quotContext_4256_; lean_object* v_currMacroScope_4257_; uint8_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_toCold_4253_ = lean_ctor_get(v_a_4123_, 0);
v_a_4254_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4252_, 1);
v_ref_4255_ = lean_ctor_get(v_a_4123_, 2);
v_quotContext_4256_ = lean_ctor_get(v_toCold_4253_, 8);
v_currMacroScope_4257_ = lean_ctor_get(v_toCold_4253_, 9);
v___x_4258_ = lean_unbox(v_a_4149_);
lean_dec(v_a_4149_);
v___x_4259_ = l_Lean_SourceInfo_fromRef(v_ref_4255_, v___x_4258_);
v___x_4260_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4261_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__6));
v___x_4262_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
lean_inc_n(v___x_4259_, 7);
v___x_4263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4259_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__9));
v___x_4265_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__10, &l_Lean_PrettyPrinter_Delaborator_delab___closed__10_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__10);
v___x_4266_ = lean_box(0);
lean_inc(v_currMacroScope_4257_);
lean_inc(v_quotContext_4256_);
v___x_4267_ = l_Lean_addMacroScope(v_quotContext_4256_, v___x_4266_, v_currMacroScope_4257_);
v___x_4268_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4259_);
lean_ctor_set(v___x_4269_, 1, v___x_4265_);
lean_ctor_set(v___x_4269_, 2, v___x_4267_);
lean_ctor_set(v___x_4269_, 3, v___x_4268_);
v___x_4270_ = l_Lean_Syntax_node1(v___x_4259_, v___x_4264_, v___x_4269_);
v___x_4271_ = l_Lean_Syntax_node2(v___x_4259_, v___x_4261_, v___x_4263_, v___x_4270_);
v___x_4272_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4259_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_));
v___x_4275_ = l_Lean_Syntax_node1(v___x_4259_, v___x_4274_, v_a_4254_);
v___x_4276_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4259_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = l_Lean_Syntax_node5(v___x_4259_, v___x_4260_, v___x_4271_, v_a_4240_, v___x_4273_, v___x_4275_, v___x_4277_);
v___x_4279_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4278_, v_a_4119_);
return v___x_4279_;
}
else
{
lean_dec(v_a_4240_);
lean_dec(v_a_4149_);
return v___x_4252_;
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_a_4240_);
lean_dec(v_a_4149_);
v_a_4281_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4242_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4242_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_dec(v_a_4149_);
return v___x_4239_;
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_4149_);
lean_dec(v_a_4147_);
v_a_4289_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4151_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4151_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_dec(v_a_4149_);
lean_dec(v_a_4147_);
v___x_4297_ = lean_box(0);
v___x_4298_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4297_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4123_);
return v___x_4298_;
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_a_4147_);
v_a_4299_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4148_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4148_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4146_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4146_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
}
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = lean_box(2);
v___x_4318_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4317_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4123_);
return v___x_4318_;
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec(v___x_4128_);
v_a_4319_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4130_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4130_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
v_a_4327_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4127_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4127_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4335_, lean_object* v_msg_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4343_, lean_object* v_msg_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4343_, v_msg_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4361_, v_x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4372_, lean_object* v_prec_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4382_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4381_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4395_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4395_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4395_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v_mctx_4388_; lean_object* v___x_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4387_ = lean_st_ref_get(v_a_4377_);
v_mctx_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc_ref(v_mctx_4388_);
lean_dec(v___x_4387_);
v___x_4389_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4389_, 0, v_mctx_4388_);
v___x_4390_ = lean_unbox(v_a_4383_);
lean_dec(v_a_4383_);
v___x_4391_ = l_Lean_Level_quote(v_l_4372_, v_prec_4373_, v___x_4390_, v___x_4389_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4391_);
v___x_4393_ = v___x_4385_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_l_4372_);
v_a_4396_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4382_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4382_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4404_, lean_object* v_prec_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4404_, v_prec_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_prec_4405_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_(uint8_t v_x_4414_, lean_object* v_stx_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc_n(v_a_4420_, 2);
lean_dec_ref_known(v___x_4419_, 1);
v___x_4421_ = lean_box(0);
v___x_4422_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4420_, v___x_4421_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4424_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc_n(v_a_4423_, 2);
lean_dec_ref_known(v___x_4422_, 1);
v___x_4424_ = l_Lean_Core_checkDeprecatedAt(v_a_4420_, v_a_4423_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4424_) == 0)
{
uint8_t v___x_4425_; lean_object* v___x_4426_; 
lean_dec_ref_known(v___x_4424_, 1);
v___x_4425_ = 0;
lean_inc(v_a_4423_);
v___x_4426_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1(v_a_4423_, v___x_4425_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v___x_4426_, 0);
lean_dec(v_unused_4434_);
v___x_4428_ = v___x_4426_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_dec(v___x_4426_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v_a_4423_);
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4423_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_a_4423_);
v_a_4435_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4426_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4426_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec(v_a_4423_);
v_a_4443_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4424_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4424_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_dec(v_a_4420_);
return v___x_4422_;
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4419_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4419_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2____boxed(lean_object* v_x_4459_, lean_object* v_stx_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v_x_485__boxed_4464_; lean_object* v_res_4465_; 
v_x_485__boxed_4464_ = lean_unbox(v_x_4459_);
v_res_4465_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_(v_x_485__boxed_4464_, v_stx_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_));
v___x_4491_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_));
v___x_4492_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4490_, v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2____boxed(lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_();
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4497_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_));
v___x_4498_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4499_ = l_Lean_addBuiltinDocString(v___x_4497_, v___x_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_));
v___x_4529_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4530_ = l_Lean_addBuiltinDeclarationRanges(v___x_4528_, v___x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; lean_object* v_mctx_4537_; lean_object* v___x_4538_; lean_object* v_fst_4539_; lean_object* v_snd_4540_; lean_object* v___x_4541_; lean_object* v_cache_4542_; lean_object* v_zetaDeltaFVarIds_4543_; lean_object* v_postponed_4544_; lean_object* v_diag_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4554_; 
v___x_4536_ = lean_st_ref_get(v___y_4534_);
v_mctx_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_ref(v_mctx_4537_);
lean_dec(v___x_4536_);
v___x_4538_ = lean_instantiate_level_mvars(v_mctx_4537_, v_l_4533_);
v_fst_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_fst_4539_);
v_snd_4540_ = lean_ctor_get(v___x_4538_, 1);
lean_inc(v_snd_4540_);
lean_dec_ref(v___x_4538_);
v___x_4541_ = lean_st_ref_take(v___y_4534_);
v_cache_4542_ = lean_ctor_get(v___x_4541_, 1);
v_zetaDeltaFVarIds_4543_ = lean_ctor_get(v___x_4541_, 2);
v_postponed_4544_ = lean_ctor_get(v___x_4541_, 3);
v_diag_4545_ = lean_ctor_get(v___x_4541_, 4);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v___x_4541_, 0);
lean_dec(v_unused_4555_);
v___x_4547_ = v___x_4541_;
v_isShared_4548_ = v_isSharedCheck_4554_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_diag_4545_);
lean_inc(v_postponed_4544_);
lean_inc(v_zetaDeltaFVarIds_4543_);
lean_inc(v_cache_4542_);
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4554_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v_fst_4539_);
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_fst_4539_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_cache_4542_);
lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_zetaDeltaFVarIds_4543_);
lean_ctor_set(v_reuseFailAlloc_4553_, 3, v_postponed_4544_);
lean_ctor_set(v_reuseFailAlloc_4553_, 4, v_diag_4545_);
v___x_4550_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = lean_st_ref_put(v___y_4534_, v___x_4550_);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_snd_4540_);
return v___x_4552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4556_, v___y_4557_);
lean_dec(v___y_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4560_, v___y_4562_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4574_, lean_object* v_prec_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_l_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4578_);
v___x_4593_ = l_Lean_getPPInstantiateMVars(v___x_4592_);
lean_dec_ref(v___x_4592_);
if (v___x_4593_ == 0)
{
v_l_4582_ = v_l_4574_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4594_; lean_object* v_a_4595_; 
v___x_4594_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4574_, v_a_4577_);
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v_l_4582_ = v_a_4595_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
goto v___jp_4581_;
}
v___jp_4581_:
{
lean_object* v___x_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; lean_object* v_mctx_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4585_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4584_);
v___x_4586_ = l_Lean_getPPMVarsLevels(v___x_4585_);
lean_dec_ref(v___x_4585_);
v___x_4587_ = lean_st_ref_get(v___y_4583_);
v_mctx_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc_ref(v_mctx_4588_);
lean_dec(v___x_4587_);
v___x_4589_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4589_, 0, v_mctx_4588_);
v___x_4590_ = l_Lean_Level_quote(v_l_4582_, v_prec_4575_, v___x_4586_, v___x_4589_);
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4596_, lean_object* v_prec_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Lean_PrettyPrinter_delabLevel(v_l_4596_, v_prec_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_prec_4597_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___f_4611_; lean_object* v___x_8213__overap_4612_; lean_object* v___x_4613_; 
v___f_4611_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8213__overap_4612_ = lean_panic_fn_borrowed(v___f_4611_, v_msg_4605_);
lean_inc(v___y_4609_);
lean_inc_ref(v___y_4608_);
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
v___x_4613_ = lean_apply_5(v___x_8213__overap_4612_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, lean_box(0));
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4621_, lean_object* v_msg_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4629_, lean_object* v_msg_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4629_, v_msg_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4637_, lean_object* v_opt_4638_){
_start:
{
lean_object* v_name_4639_; lean_object* v_defValue_4640_; lean_object* v_map_4641_; lean_object* v___x_4642_; 
v_name_4639_ = lean_ctor_get(v_opt_4638_, 0);
v_defValue_4640_ = lean_ctor_get(v_opt_4638_, 1);
v_map_4641_ = lean_ctor_get(v_opts_4637_, 0);
v___x_4642_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4641_, v_name_4639_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_inc(v_defValue_4640_);
return v_defValue_4640_;
}
else
{
lean_object* v_val_4643_; 
v_val_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_val_4643_);
lean_dec_ref_known(v___x_4642_, 1);
if (lean_obj_tag(v_val_4643_) == 3)
{
lean_object* v_v_4644_; 
v_v_4644_ = lean_ctor_get(v_val_4643_, 0);
lean_inc(v_v_4644_);
lean_dec_ref_known(v_val_4643_, 1);
return v_v_4644_;
}
else
{
lean_dec(v_val_4643_);
lean_inc(v_defValue_4640_);
return v_defValue_4640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4645_, lean_object* v_opt_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4645_, v_opt_4646_);
lean_dec_ref(v_opt_4646_);
lean_dec_ref(v_opts_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(lean_object* v_e_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___x_4651_; 
v___x_4651_ = l_Lean_Expr_hasMVar(v_e_4648_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_e_4648_);
return v___x_4652_;
}
else
{
lean_object* v___x_4653_; lean_object* v_mctx_4654_; lean_object* v___x_4655_; lean_object* v_fst_4656_; lean_object* v_snd_4657_; lean_object* v___x_4658_; lean_object* v_cache_4659_; lean_object* v_zetaDeltaFVarIds_4660_; lean_object* v_postponed_4661_; lean_object* v_diag_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4671_; 
v___x_4653_ = lean_st_ref_get(v___y_4649_);
v_mctx_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc_ref(v_mctx_4654_);
lean_dec(v___x_4653_);
v___x_4655_ = l_Lean_instantiateMVarsCore(v_mctx_4654_, v_e_4648_);
v_fst_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_fst_4656_);
v_snd_4657_ = lean_ctor_get(v___x_4655_, 1);
lean_inc(v_snd_4657_);
lean_dec_ref(v___x_4655_);
v___x_4658_ = lean_st_ref_take(v___y_4649_);
v_cache_4659_ = lean_ctor_get(v___x_4658_, 1);
v_zetaDeltaFVarIds_4660_ = lean_ctor_get(v___x_4658_, 2);
v_postponed_4661_ = lean_ctor_get(v___x_4658_, 3);
v_diag_4662_ = lean_ctor_get(v___x_4658_, 4);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4671_ == 0)
{
lean_object* v_unused_4672_; 
v_unused_4672_ = lean_ctor_get(v___x_4658_, 0);
lean_dec(v_unused_4672_);
v___x_4664_ = v___x_4658_;
v_isShared_4665_ = v_isSharedCheck_4671_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_diag_4662_);
lean_inc(v_postponed_4661_);
lean_inc(v_zetaDeltaFVarIds_4660_);
lean_inc(v_cache_4659_);
lean_dec(v___x_4658_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4671_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v_snd_4657_);
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_snd_4657_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_cache_4659_);
lean_ctor_set(v_reuseFailAlloc_4670_, 2, v_zetaDeltaFVarIds_4660_);
lean_ctor_set(v_reuseFailAlloc_4670_, 3, v_postponed_4661_);
lean_ctor_set(v_reuseFailAlloc_4670_, 4, v_diag_4662_);
v___x_4667_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = lean_st_ref_put(v___y_4649_, v___x_4667_);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v_fst_4656_);
return v___x_4669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg___boxed(lean_object* v_e_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4673_, v___y_4674_);
lean_dec(v___y_4674_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_e_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_e_4677_, v___y_4679_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_e_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2(v_e_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_opts_4691_, lean_object* v_opt_4692_){
_start:
{
lean_object* v_name_4693_; lean_object* v_map_4694_; lean_object* v___x_4695_; 
v_name_4693_ = lean_ctor_get(v_opt_4692_, 0);
v_map_4694_ = lean_ctor_get(v_opts_4691_, 0);
v___x_4695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4694_, v_name_4693_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v___x_4696_; 
v___x_4696_ = lean_box(0);
return v___x_4696_;
}
else
{
lean_object* v_val_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4707_; 
v_val_4697_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4699_ = v___x_4695_;
v_isShared_4700_ = v_isSharedCheck_4707_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_val_4697_);
lean_dec(v___x_4695_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4707_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
if (lean_obj_tag(v_val_4697_) == 1)
{
uint8_t v_v_4701_; lean_object* v___x_4702_; lean_object* v___x_4704_; 
v_v_4701_ = lean_ctor_get_uint8(v_val_4697_, 0);
lean_dec_ref_known(v_val_4697_, 0);
v___x_4702_ = lean_box(v_v_4701_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4702_);
v___x_4704_ = v___x_4699_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4702_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
else
{
lean_object* v___x_4706_; 
lean_del_object(v___x_4699_);
lean_dec(v_val_4697_);
v___x_4706_ = lean_box(0);
return v___x_4706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_opts_4708_, lean_object* v_opt_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(v_opts_4708_, v_opt_4709_);
lean_dec_ref(v_opt_4709_);
lean_dec_ref(v_opts_4708_);
return v_res_4710_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_x_4711_, lean_object* v_x_4712_){
_start:
{
if (lean_obj_tag(v_x_4711_) == 0)
{
if (lean_obj_tag(v_x_4712_) == 0)
{
uint8_t v___x_4713_; 
v___x_4713_ = 1;
return v___x_4713_;
}
else
{
uint8_t v___x_4714_; 
v___x_4714_ = 0;
return v___x_4714_;
}
}
else
{
if (lean_obj_tag(v_x_4712_) == 0)
{
uint8_t v___x_4715_; 
v___x_4715_ = 0;
return v___x_4715_;
}
else
{
lean_object* v_val_4716_; uint8_t v___x_4717_; 
v_val_4716_ = lean_ctor_get(v_x_4712_, 0);
v___x_4717_ = lean_unbox(v_val_4716_);
if (v___x_4717_ == 0)
{
lean_object* v_val_4718_; uint8_t v___x_4719_; 
v_val_4718_ = lean_ctor_get(v_x_4711_, 0);
v___x_4719_ = lean_unbox(v_val_4718_);
if (v___x_4719_ == 0)
{
uint8_t v___x_4720_; 
v___x_4720_ = 1;
return v___x_4720_;
}
else
{
uint8_t v___x_4721_; 
v___x_4721_ = lean_unbox(v_val_4716_);
return v___x_4721_;
}
}
else
{
lean_object* v_val_4722_; uint8_t v___x_4723_; 
v_val_4722_ = lean_ctor_get(v_x_4711_, 0);
v___x_4723_ = lean_unbox(v_val_4722_);
return v___x_4723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_x_4724_, lean_object* v_x_4725_){
_start:
{
uint8_t v_res_4726_; lean_object* v_r_4727_; 
v_res_4726_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(v_x_4724_, v_x_4725_);
lean_dec(v_x_4725_);
lean_dec(v_x_4724_);
v_r_4727_ = lean_box(v_res_4726_);
return v_r_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_cls_4728_, lean_object* v_msg_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_ref_4735_; lean_object* v___x_4736_; lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4782_; 
v_ref_4735_ = lean_ctor_get(v___y_4732_, 2);
v___x_4736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4782_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4782_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v_traceState_4742_; lean_object* v_env_4743_; lean_object* v_nextMacroScope_4744_; lean_object* v_ngen_4745_; lean_object* v_auxDeclNGen_4746_; lean_object* v_cache_4747_; lean_object* v_recordedDeps_4748_; lean_object* v_messages_4749_; lean_object* v_infoState_4750_; lean_object* v_snapshotTasks_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4781_; 
v___x_4741_ = lean_st_ref_take(v___y_4733_);
v_traceState_4742_ = lean_ctor_get(v___x_4741_, 4);
v_env_4743_ = lean_ctor_get(v___x_4741_, 0);
v_nextMacroScope_4744_ = lean_ctor_get(v___x_4741_, 1);
v_ngen_4745_ = lean_ctor_get(v___x_4741_, 2);
v_auxDeclNGen_4746_ = lean_ctor_get(v___x_4741_, 3);
v_cache_4747_ = lean_ctor_get(v___x_4741_, 5);
v_recordedDeps_4748_ = lean_ctor_get(v___x_4741_, 6);
v_messages_4749_ = lean_ctor_get(v___x_4741_, 7);
v_infoState_4750_ = lean_ctor_get(v___x_4741_, 8);
v_snapshotTasks_4751_ = lean_ctor_get(v___x_4741_, 9);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4753_ = v___x_4741_;
v_isShared_4754_ = v_isSharedCheck_4781_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_snapshotTasks_4751_);
lean_inc(v_infoState_4750_);
lean_inc(v_messages_4749_);
lean_inc(v_recordedDeps_4748_);
lean_inc(v_cache_4747_);
lean_inc(v_traceState_4742_);
lean_inc(v_auxDeclNGen_4746_);
lean_inc(v_ngen_4745_);
lean_inc(v_nextMacroScope_4744_);
lean_inc(v_env_4743_);
lean_dec(v___x_4741_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4781_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
uint64_t v_tid_4755_; lean_object* v_traces_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4780_; 
v_tid_4755_ = lean_ctor_get_uint64(v_traceState_4742_, sizeof(void*)*1);
v_traces_4756_ = lean_ctor_get(v_traceState_4742_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v_traceState_4742_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4758_ = v_traceState_4742_;
v_isShared_4759_ = v_isSharedCheck_4780_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_traces_4756_);
lean_dec(v_traceState_4742_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4780_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; double v___x_4762_; uint8_t v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4760_ = lean_box(0);
v___x_4761_ = lean_box(0);
v___x_4762_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_4763_ = 0;
v___x_4764_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4765_, 0, v_cls_4728_);
lean_ctor_set(v___x_4765_, 1, v___x_4761_);
lean_ctor_set(v___x_4765_, 2, v___x_4764_);
lean_ctor_set_float(v___x_4765_, sizeof(void*)*3, v___x_4762_);
lean_ctor_set_float(v___x_4765_, sizeof(void*)*3 + 8, v___x_4762_);
lean_ctor_set_uint8(v___x_4765_, sizeof(void*)*3 + 16, v___x_4763_);
v___x_4766_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_4767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v_a_4737_);
lean_ctor_set(v___x_4767_, 2, v___x_4766_);
lean_inc(v_ref_4735_);
v___x_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4768_, 0, v_ref_4735_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = l_Lean_PersistentArray_push___redArg(v_traces_4756_, v___x_4768_);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 0, v___x_4769_);
v___x_4771_ = v___x_4758_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4769_);
lean_ctor_set_uint64(v_reuseFailAlloc_4779_, sizeof(void*)*1, v_tid_4755_);
v___x_4771_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 4, v___x_4771_);
v___x_4773_ = v___x_4753_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_env_4743_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_nextMacroScope_4744_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_ngen_4745_);
lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_auxDeclNGen_4746_);
lean_ctor_set(v_reuseFailAlloc_4778_, 4, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4778_, 5, v_cache_4747_);
lean_ctor_set(v_reuseFailAlloc_4778_, 6, v_recordedDeps_4748_);
lean_ctor_set(v_reuseFailAlloc_4778_, 7, v_messages_4749_);
lean_ctor_set(v_reuseFailAlloc_4778_, 8, v_infoState_4750_);
lean_ctor_set(v_reuseFailAlloc_4778_, 9, v_snapshotTasks_4751_);
v___x_4773_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4774_ = lean_st_ref_put(v___y_4733_, v___x_4773_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4760_);
v___x_4776_ = v___x_4739_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4760_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_cls_4783_, lean_object* v_msg_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v_cls_4783_, v_msg_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(lean_object* v_o_4791_, lean_object* v_k_4792_, uint8_t v_v_4793_){
_start:
{
lean_object* v_map_4794_; uint8_t v_hasTrace_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4809_; 
v_map_4794_ = lean_ctor_get(v_o_4791_, 0);
v_hasTrace_4795_ = lean_ctor_get_uint8(v_o_4791_, sizeof(void*)*1);
v_isSharedCheck_4809_ = !lean_is_exclusive(v_o_4791_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4797_ = v_o_4791_;
v_isShared_4798_ = v_isSharedCheck_4809_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_map_4794_);
lean_dec(v_o_4791_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4809_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4799_, 0, v_v_4793_);
lean_inc(v_k_4792_);
v___x_4800_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4792_, v___x_4799_, v_map_4794_);
if (v_hasTrace_4795_ == 0)
{
lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4804_; 
v___x_4801_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4802_ = l_Lean_Name_isPrefixOf(v___x_4801_, v_k_4792_);
lean_dec(v_k_4792_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4800_);
v___x_4804_ = v___x_4797_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4800_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_ctor_set_uint8(v___x_4804_, sizeof(void*)*1, v___x_4802_);
return v___x_4804_;
}
}
else
{
lean_object* v___x_4807_; 
lean_dec(v_k_4792_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4800_);
v___x_4807_ = v___x_4797_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4800_);
lean_ctor_set_uint8(v_reuseFailAlloc_4808_, sizeof(void*)*1, v_hasTrace_4795_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5___boxed(lean_object* v_o_4810_, lean_object* v_k_4811_, lean_object* v_v_4812_){
_start:
{
uint8_t v_v_boxed_4813_; lean_object* v_res_4814_; 
v_v_boxed_4813_ = lean_unbox(v_v_4812_);
v_res_4814_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(v_o_4810_, v_k_4811_, v_v_boxed_4813_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4815_, lean_object* v_opt_4816_, uint8_t v_val_4817_){
_start:
{
lean_object* v_name_4818_; lean_object* v___x_4819_; 
v_name_4818_ = lean_ctor_get(v_opt_4816_, 0);
lean_inc(v_name_4818_);
lean_dec_ref(v_opt_4816_);
v___x_4819_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5_spec__5(v_opts_4815_, v_name_4818_, v_val_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4820_, lean_object* v_opt_4821_, lean_object* v_val_4822_){
_start:
{
uint8_t v_val_boxed_4823_; lean_object* v_res_4824_; 
v_val_boxed_4823_ = lean_unbox(v_val_4822_);
v_res_4824_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4820_, v_opt_4821_, v_val_boxed_4823_);
return v_res_4824_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__0(void){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4825_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4826_ = lean_unsigned_to_nat(2u);
v___x_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
lean_ctor_set(v___x_4827_, 1, v___x_4825_);
return v___x_4827_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4828_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__0, &l_Lean_PrettyPrinter_delabCore___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__0);
v___x_4829_ = lean_box(1);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
lean_ctor_set(v___x_4831_, 1, v___x_4829_);
lean_ctor_set(v___x_4831_, 2, v___x_4828_);
return v___x_4831_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4835_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__4));
v___x_4836_ = lean_unsigned_to_nat(18u);
v___x_4837_ = lean_unsigned_to_nat(541u);
v___x_4838_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__3));
v___x_4839_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4840_ = l_mkPanicMessageWithDecl(v___x_4839_, v___x_4838_, v___x_4837_, v___x_4836_, v___x_4835_);
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4846_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4847_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__11));
v___x_4848_ = l_Lean_Name_append(v___x_4847_, v___x_4846_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4849_, lean_object* v_optionsPerPos_4850_, lean_object* v_delab_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_fst_4858_; lean_object* v_snd_4859_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v_optionsPerPos_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4928_; lean_object* v_e_4929_; lean_object* v___y_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4947_; lean_object* v_e_4948_; lean_object* v___y_4949_; lean_object* v___y_4950_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4849_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; uint8_t v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; uint16_t v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; uint8_t v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; uint16_t v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; uint8_t v___y_5006_; uint8_t v___y_5029_; lean_object* v___y_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v_opts_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v_toCold_5085_; lean_object* v_options_5086_; uint8_t v_hasTrace_5087_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
v_toCold_5085_ = lean_ctor_get(v_a_4854_, 0);
v_options_5086_ = lean_ctor_get(v_toCold_5085_, 2);
v_hasTrace_5087_ = lean_ctor_get_uint8(v_options_5086_, sizeof(void*)*1);
if (v_hasTrace_5087_ == 0)
{
v___y_5058_ = v_a_4852_;
v___y_5059_ = v_a_4853_;
v___y_5060_ = v_a_4854_;
v___y_5061_ = v_a_4855_;
goto v___jp_5057_;
}
else
{
lean_object* v_inheritedTraceOptions_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; 
v_inheritedTraceOptions_5088_ = lean_ctor_get(v_toCold_5085_, 11);
v___x_5089_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5090_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5088_, v_options_5086_, v___x_5090_);
if (v___x_5091_ == 0)
{
v___y_5058_ = v_a_4852_;
v___y_5059_ = v_a_4853_;
v___y_5060_ = v_a_4854_;
v___y_5061_ = v_a_4855_;
goto v___jp_5057_;
}
else
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5092_ = lean_expr_dbg_to_string(v_a_4965_);
v___x_5093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
v___x_5094_ = l_Lean_MessageData_ofFormat(v___x_5093_);
v___x_5095_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5089_, v___x_5094_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_dec_ref_known(v___x_5095_, 1);
v___y_5058_ = v_a_4852_;
v___y_5059_ = v_a_4853_;
v___y_5060_ = v_a_4854_;
v___y_5061_ = v_a_4855_;
goto v___jp_5057_;
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_a_4965_);
lean_dec_ref(v_delab_4851_);
lean_dec(v_optionsPerPos_4850_);
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5095_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5095_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
v___jp_4966_:
{
lean_object* v_toCold_4975_; lean_object* v_currRecDepth_4976_; lean_object* v_ref_4977_; uint8_t v_suppressElabErrors_4978_; uint8_t v_checkDeprecated_4979_; uint8_t v_isRecordingDeps_4980_; lean_object* v_fileName_4981_; lean_object* v_fileMap_4982_; lean_object* v_currNamespace_4983_; lean_object* v_openDecls_4984_; lean_object* v_initHeartbeats_4985_; lean_object* v_maxHeartbeats_4986_; lean_object* v_quotContext_4987_; lean_object* v_currMacroScope_4988_; lean_object* v_cancelTk_x3f_4989_; lean_object* v_inheritedTraceOptions_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_toCold_4975_ = lean_ctor_get(v___y_4973_, 0);
v_currRecDepth_4976_ = lean_ctor_get(v___y_4973_, 1);
v_ref_4977_ = lean_ctor_get(v___y_4973_, 2);
v_suppressElabErrors_4978_ = lean_ctor_get_uint8(v___y_4973_, sizeof(void*)*3 + 2);
v_checkDeprecated_4979_ = lean_ctor_get_uint8(v___y_4973_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4980_ = lean_ctor_get_uint8(v___y_4973_, sizeof(void*)*3 + 4);
v_fileName_4981_ = lean_ctor_get(v_toCold_4975_, 0);
v_fileMap_4982_ = lean_ctor_get(v_toCold_4975_, 1);
v_currNamespace_4983_ = lean_ctor_get(v_toCold_4975_, 4);
v_openDecls_4984_ = lean_ctor_get(v_toCold_4975_, 5);
v_initHeartbeats_4985_ = lean_ctor_get(v_toCold_4975_, 6);
v_maxHeartbeats_4986_ = lean_ctor_get(v_toCold_4975_, 7);
v_quotContext_4987_ = lean_ctor_get(v_toCold_4975_, 8);
v_currMacroScope_4988_ = lean_ctor_get(v_toCold_4975_, 9);
v_cancelTk_x3f_4989_ = lean_ctor_get(v_toCold_4975_, 10);
v_inheritedTraceOptions_4990_ = lean_ctor_get(v_toCold_4975_, 11);
v___x_4991_ = l_Lean_maxRecDepth;
v___x_4992_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v___y_4972_, v___x_4991_);
lean_inc_ref(v_inheritedTraceOptions_4990_);
lean_inc(v_cancelTk_x3f_4989_);
lean_inc(v_currMacroScope_4988_);
lean_inc(v_quotContext_4987_);
lean_inc(v_maxHeartbeats_4986_);
lean_inc(v_initHeartbeats_4985_);
lean_inc(v_openDecls_4984_);
lean_inc(v_currNamespace_4983_);
lean_inc_ref(v_fileMap_4982_);
lean_inc_ref(v_fileName_4981_);
v___x_4993_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4993_, 0, v_fileName_4981_);
lean_ctor_set(v___x_4993_, 1, v_fileMap_4982_);
lean_ctor_set(v___x_4993_, 2, v___y_4972_);
lean_ctor_set(v___x_4993_, 3, v___x_4992_);
lean_ctor_set(v___x_4993_, 4, v_currNamespace_4983_);
lean_ctor_set(v___x_4993_, 5, v_openDecls_4984_);
lean_ctor_set(v___x_4993_, 6, v_initHeartbeats_4985_);
lean_ctor_set(v___x_4993_, 7, v_maxHeartbeats_4986_);
lean_ctor_set(v___x_4993_, 8, v_quotContext_4987_);
lean_ctor_set(v___x_4993_, 9, v_currMacroScope_4988_);
lean_ctor_set(v___x_4993_, 10, v_cancelTk_x3f_4989_);
lean_ctor_set(v___x_4993_, 11, v_inheritedTraceOptions_4990_);
lean_inc(v_ref_4977_);
lean_inc(v_currRecDepth_4976_);
v___x_4994_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
lean_ctor_set(v___x_4994_, 1, v_currRecDepth_4976_);
lean_ctor_set(v___x_4994_, 2, v_ref_4977_);
lean_ctor_set_uint16(v___x_4994_, sizeof(void*)*3, v___y_4971_);
lean_ctor_set_uint8(v___x_4994_, sizeof(void*)*3 + 2, v_suppressElabErrors_4978_);
lean_ctor_set_uint8(v___x_4994_, sizeof(void*)*3 + 3, v_checkDeprecated_4979_);
lean_ctor_set_uint8(v___x_4994_, sizeof(void*)*3 + 4, v_isRecordingDeps_4980_);
if (v___y_4967_ == 0)
{
v___y_4947_ = v___y_4969_;
v_e_4948_ = v_a_4965_;
v___y_4949_ = v___y_4968_;
v___y_4950_ = v___y_4970_;
v___y_4951_ = v___x_4994_;
v___y_4952_ = v___y_4974_;
goto v___jp_4946_;
}
else
{
lean_object* v___x_4995_; lean_object* v_a_4996_; 
v___x_4995_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__2___redArg(v_a_4965_, v___y_4970_);
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref(v___x_4995_);
v___y_4947_ = v___y_4969_;
v_e_4948_ = v_a_4996_;
v___y_4949_ = v___y_4968_;
v___y_4950_ = v___y_4970_;
v___y_4951_ = v___x_4994_;
v___y_4952_ = v___y_4974_;
goto v___jp_4946_;
}
}
v___jp_4997_:
{
lean_object* v___x_5007_; lean_object* v_env_5008_; lean_object* v_nextMacroScope_5009_; lean_object* v_ngen_5010_; lean_object* v_auxDeclNGen_5011_; lean_object* v_traceState_5012_; lean_object* v_recordedDeps_5013_; lean_object* v_messages_5014_; lean_object* v_infoState_5015_; lean_object* v_snapshotTasks_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5026_; 
v___x_5007_ = lean_st_ref_take(v___y_4999_);
v_env_5008_ = lean_ctor_get(v___x_5007_, 0);
v_nextMacroScope_5009_ = lean_ctor_get(v___x_5007_, 1);
v_ngen_5010_ = lean_ctor_get(v___x_5007_, 2);
v_auxDeclNGen_5011_ = lean_ctor_get(v___x_5007_, 3);
v_traceState_5012_ = lean_ctor_get(v___x_5007_, 4);
v_recordedDeps_5013_ = lean_ctor_get(v___x_5007_, 6);
v_messages_5014_ = lean_ctor_get(v___x_5007_, 7);
v_infoState_5015_ = lean_ctor_get(v___x_5007_, 8);
v_snapshotTasks_5016_ = lean_ctor_get(v___x_5007_, 9);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5026_ == 0)
{
lean_object* v_unused_5027_; 
v_unused_5027_ = lean_ctor_get(v___x_5007_, 5);
lean_dec(v_unused_5027_);
v___x_5018_ = v___x_5007_;
v_isShared_5019_ = v_isSharedCheck_5026_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_snapshotTasks_5016_);
lean_inc(v_infoState_5015_);
lean_inc(v_messages_5014_);
lean_inc(v_recordedDeps_5013_);
lean_inc(v_traceState_5012_);
lean_inc(v_auxDeclNGen_5011_);
lean_inc(v_ngen_5010_);
lean_inc(v_nextMacroScope_5009_);
lean_inc(v_env_5008_);
lean_dec(v___x_5007_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5026_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5020_ = l_Lean_Kernel_enableDiag(v_env_5008_, v___y_5006_);
v___x_5021_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2__spec__1_spec__2___closed__1);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 5, v___x_5021_);
lean_ctor_set(v___x_5018_, 0, v___x_5020_);
v___x_5023_ = v___x_5018_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5020_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_nextMacroScope_5009_);
lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_ngen_5010_);
lean_ctor_set(v_reuseFailAlloc_5025_, 3, v_auxDeclNGen_5011_);
lean_ctor_set(v_reuseFailAlloc_5025_, 4, v_traceState_5012_);
lean_ctor_set(v_reuseFailAlloc_5025_, 5, v___x_5021_);
lean_ctor_set(v_reuseFailAlloc_5025_, 6, v_recordedDeps_5013_);
lean_ctor_set(v_reuseFailAlloc_5025_, 7, v_messages_5014_);
lean_ctor_set(v_reuseFailAlloc_5025_, 8, v_infoState_5015_);
lean_ctor_set(v_reuseFailAlloc_5025_, 9, v_snapshotTasks_5016_);
v___x_5023_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5024_; 
v___x_5024_ = lean_st_ref_put(v___y_4999_, v___x_5023_);
v___y_4967_ = v___y_4998_;
v___y_4968_ = v___y_5000_;
v___y_4969_ = v___y_5003_;
v___y_4970_ = v___y_5002_;
v___y_4971_ = v___y_5001_;
v___y_4972_ = v___y_5004_;
v___y_4973_ = v___y_5005_;
v___y_4974_ = v___y_4999_;
goto v___jp_4966_;
}
}
}
v___jp_5028_:
{
uint16_t v___x_5036_; lean_object* v___x_5037_; lean_object* v_env_5038_; uint8_t v___x_5039_; uint16_t v___x_5040_; uint16_t v___x_5041_; uint16_t v___x_5042_; uint8_t v___x_5043_; 
v___x_5036_ = l_Lean_OptionFlags_ofOptions(v___y_5035_);
v___x_5037_ = lean_st_ref_get(v___y_5030_);
v_env_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc_ref(v_env_5038_);
lean_dec(v___x_5037_);
v___x_5039_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5038_);
lean_dec_ref(v_env_5038_);
v___x_5040_ = 512;
v___x_5041_ = lean_uint16_land(v___x_5036_, v___x_5040_);
v___x_5042_ = 0;
v___x_5043_ = lean_uint16_dec_eq(v___x_5041_, v___x_5042_);
if (v___x_5043_ == 0)
{
if (v___x_5039_ == 0)
{
uint8_t v___x_5044_; 
v___x_5044_ = 1;
v___y_4998_ = v___y_5029_;
v___y_4999_ = v___y_5030_;
v___y_5000_ = v___y_5031_;
v___y_5001_ = v___x_5036_;
v___y_5002_ = v___y_5032_;
v___y_5003_ = v___y_5033_;
v___y_5004_ = v___y_5035_;
v___y_5005_ = v___y_5034_;
v___y_5006_ = v___x_5044_;
goto v___jp_4997_;
}
else
{
v___y_4967_ = v___y_5029_;
v___y_4968_ = v___y_5031_;
v___y_4969_ = v___y_5033_;
v___y_4970_ = v___y_5032_;
v___y_4971_ = v___x_5036_;
v___y_4972_ = v___y_5035_;
v___y_4973_ = v___y_5034_;
v___y_4974_ = v___y_5030_;
goto v___jp_4966_;
}
}
else
{
if (v___x_5039_ == 0)
{
v___y_4967_ = v___y_5029_;
v___y_4968_ = v___y_5031_;
v___y_4969_ = v___y_5033_;
v___y_4970_ = v___y_5032_;
v___y_4971_ = v___x_5036_;
v___y_4972_ = v___y_5035_;
v___y_4973_ = v___y_5034_;
v___y_4974_ = v___y_5030_;
goto v___jp_4966_;
}
else
{
uint8_t v___x_5045_; 
v___x_5045_ = 0;
v___y_4998_ = v___y_5029_;
v___y_4999_ = v___y_5030_;
v___y_5000_ = v___y_5031_;
v___y_5001_ = v___x_5036_;
v___y_5002_ = v___y_5032_;
v___y_5003_ = v___y_5033_;
v___y_5004_ = v___y_5035_;
v___y_5005_ = v___y_5034_;
v___y_5006_ = v___x_5045_;
goto v___jp_4997_;
}
}
}
v___jp_5046_:
{
lean_object* v_toCold_5052_; uint8_t v_isRecordingDeps_5053_; uint8_t v___x_5054_; 
v_toCold_5052_ = lean_ctor_get(v___y_5050_, 0);
v_isRecordingDeps_5053_ = lean_ctor_get_uint8(v___y_5050_, sizeof(void*)*3 + 4);
v___x_5054_ = l_Lean_getPPInstantiateMVars(v_opts_5047_);
if (v_isRecordingDeps_5053_ == 0)
{
lean_inc_ref(v_opts_5047_);
v___y_5029_ = v___x_5054_;
v___y_5030_ = v___y_5051_;
v___y_5031_ = v___y_5048_;
v___y_5032_ = v___y_5049_;
v___y_5033_ = v_opts_5047_;
v___y_5034_ = v___y_5050_;
v___y_5035_ = v_opts_5047_;
goto v___jp_5028_;
}
else
{
lean_object* v_options_5055_; lean_object* v___x_5056_; 
v_options_5055_ = lean_ctor_get(v_toCold_5052_, 2);
lean_inc_ref(v_options_5055_);
v___x_5056_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5055_);
v___y_5029_ = v___x_5054_;
v___y_5030_ = v___y_5051_;
v___y_5031_ = v___y_5048_;
v___y_5032_ = v___y_5049_;
v___y_5033_ = v_opts_5047_;
v___y_5034_ = v___y_5050_;
v___y_5035_ = v___x_5056_;
goto v___jp_5028_;
}
}
v___jp_5057_:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5062_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_5060_);
v___x_5063_ = l_Lean_pp_proofs;
v___x_5064_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__3(v___x_5062_, v___x_5063_);
v___x_5065_ = lean_box(0);
v___x_5066_ = l_instBEqOption_beq___at___00Lean_PrettyPrinter_delabCore_spec__4(v___x_5064_, v___x_5065_);
lean_dec(v___x_5064_);
if (v___x_5066_ == 0)
{
v_opts_5047_ = v___x_5062_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v___y_5059_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
goto v___jp_5046_;
}
else
{
uint8_t v___x_5067_; 
v___x_5067_ = l_Lean_Expr_isConst(v_a_4965_);
if (v___x_5067_ == 0)
{
lean_object* v___x_5068_; 
lean_inc(v_a_4965_);
v___x_5068_ = l_Lean_Meta_isProof(v_a_4965_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; uint8_t v___x_5070_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref_known(v___x_5068_, 1);
v___x_5070_ = lean_unbox(v_a_5069_);
lean_dec(v_a_5069_);
if (v___x_5070_ == 0)
{
v_opts_5047_ = v___x_5062_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v___y_5059_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
goto v___jp_5046_;
}
else
{
lean_object* v___x_5071_; 
v___x_5071_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__5(v___x_5062_, v___x_5063_, v___x_5066_);
v_opts_5047_ = v___x_5071_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v___y_5059_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
goto v___jp_5046_;
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5084_; 
v_a_5072_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5074_ = v___x_5068_;
v_isShared_5075_ = v_isSharedCheck_5084_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5068_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5084_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
uint8_t v___x_5076_; 
v___x_5076_ = l_Lean_Exception_isInterrupt(v_a_5072_);
if (v___x_5076_ == 0)
{
uint8_t v___x_5077_; 
lean_inc(v_a_5072_);
v___x_5077_ = l_Lean_Exception_isRuntime(v_a_5072_);
if (v___x_5077_ == 0)
{
lean_del_object(v___x_5074_);
lean_dec(v_a_5072_);
v_opts_5047_ = v___x_5062_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v___y_5059_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
goto v___jp_5046_;
}
else
{
lean_object* v___x_5079_; 
lean_dec_ref(v___x_5062_);
lean_dec(v_a_4965_);
lean_dec_ref(v_delab_4851_);
lean_dec(v_optionsPerPos_4850_);
if (v_isShared_5075_ == 0)
{
v___x_5079_ = v___x_5074_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5072_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
else
{
lean_object* v___x_5082_; 
lean_dec_ref(v___x_5062_);
lean_dec(v_a_4965_);
lean_dec_ref(v_delab_4851_);
lean_dec(v_optionsPerPos_4850_);
if (v_isShared_5075_ == 0)
{
v___x_5082_ = v___x_5074_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5072_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
else
{
v_opts_5047_ = v___x_5062_;
v___y_5048_ = v___y_5058_;
v___y_5049_ = v___y_5059_;
v___y_5050_ = v___y_5060_;
v___y_5051_ = v___y_5061_;
goto v___jp_5046_;
}
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v_delab_4851_);
lean_dec(v_optionsPerPos_4850_);
v_a_5104_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_4964_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_4964_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
v___jp_4857_:
{
lean_object* v_infos_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v_infos_4860_ = lean_ctor_get(v_snd_4859_, 1);
lean_inc(v_infos_4860_);
lean_dec_ref(v_snd_4859_);
v___x_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4861_, 0, v_fst_4858_);
lean_ctor_set(v___x_4861_, 1, v_infos_4860_);
v___x_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
return v___x_4862_;
}
v___jp_4863_:
{
lean_object* v_toCold_4871_; lean_object* v_currRecDepth_4872_; uint16_t v_optionFlags_4873_; uint8_t v_suppressElabErrors_4874_; uint8_t v_checkDeprecated_4875_; uint8_t v_isRecordingDeps_4876_; lean_object* v_currNamespace_4877_; lean_object* v_openDecls_4878_; lean_object* v_lctx_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v_toCold_4871_ = lean_ctor_get(v___y_4869_, 0);
v_currRecDepth_4872_ = lean_ctor_get(v___y_4869_, 1);
v_optionFlags_4873_ = lean_ctor_get_uint16(v___y_4869_, sizeof(void*)*3);
v_suppressElabErrors_4874_ = lean_ctor_get_uint8(v___y_4869_, sizeof(void*)*3 + 2);
v_checkDeprecated_4875_ = lean_ctor_get_uint8(v___y_4869_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4876_ = lean_ctor_get_uint8(v___y_4869_, sizeof(void*)*3 + 4);
v_currNamespace_4877_ = lean_ctor_get(v_toCold_4871_, 4);
v_openDecls_4878_ = lean_ctor_get(v_toCold_4871_, 5);
v_lctx_4879_ = lean_ctor_get(v___y_4867_, 2);
v___x_4880_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4881_ = lean_box(0);
v___x_4882_ = l_Lean_Options_getInPattern(v___y_4864_);
lean_dec_ref(v___y_4864_);
v___x_4883_ = l_Lean_SubExpr_mkRoot(v___y_4865_);
v___x_4884_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4879_);
v___x_4885_ = lean_local_ctx_num_indices(v_lctx_4879_);
lean_inc(v_openDecls_4878_);
lean_inc(v_currNamespace_4877_);
v___x_4886_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4886_, 0, v_optionsPerPos_4866_);
lean_ctor_set(v___x_4886_, 1, v_currNamespace_4877_);
lean_ctor_set(v___x_4886_, 2, v_openDecls_4878_);
lean_ctor_set(v___x_4886_, 3, v___x_4883_);
lean_ctor_set(v___x_4886_, 4, v___x_4884_);
lean_ctor_set(v___x_4886_, 5, v___x_4885_);
lean_ctor_set_uint8(v___x_4886_, sizeof(void*)*6, v___x_4882_);
v___x_4887_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__1, &l_Lean_PrettyPrinter_delabCore___redArg___closed__1_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__1);
v___x_4888_ = lean_st_mk_ref(v___x_4887_);
lean_inc(v_currRecDepth_4872_);
lean_inc_ref(v_toCold_4871_);
v___x_4889_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4889_, 0, v_toCold_4871_);
lean_ctor_set(v___x_4889_, 1, v_currRecDepth_4872_);
lean_ctor_set(v___x_4889_, 2, v___x_4881_);
lean_ctor_set_uint16(v___x_4889_, sizeof(void*)*3, v_optionFlags_4873_);
lean_ctor_set_uint8(v___x_4889_, sizeof(void*)*3 + 2, v_suppressElabErrors_4874_);
lean_ctor_set_uint8(v___x_4889_, sizeof(void*)*3 + 3, v_checkDeprecated_4875_);
lean_ctor_set_uint8(v___x_4889_, sizeof(void*)*3 + 4, v_isRecordingDeps_4876_);
lean_inc(v___y_4870_);
lean_inc(v___y_4868_);
lean_inc_ref(v___y_4867_);
lean_inc(v___x_4888_);
v___x_4890_ = lean_apply_7(v_delab_4851_, v___x_4886_, v___x_4888_, v___y_4867_, v___y_4868_, v___x_4889_, v___y_4870_, lean_box(0));
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4892_; 
lean_dec_ref(v___y_4869_);
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v___x_4892_ = lean_st_ref_get(v___x_4888_);
lean_dec(v___x_4888_);
v_fst_4858_ = v_a_4891_;
v_snd_4859_ = v___x_4892_;
goto v___jp_4857_;
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4926_; 
lean_dec(v___x_4888_);
v_a_4893_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4895_ = v___x_4890_;
v_isShared_4896_ = v_isSharedCheck_4926_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4890_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4926_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
uint8_t v___x_4897_; 
v___x_4897_ = l_Lean_Exception_isInterrupt(v_a_4893_);
if (v___x_4897_ == 0)
{
uint8_t v___x_4898_; 
lean_inc(v_a_4893_);
v___x_4898_ = l_Lean_Exception_isRuntime(v_a_4893_);
if (v___x_4898_ == 0)
{
if (lean_obj_tag(v_a_4893_) == 0)
{
lean_object* v___x_4900_; 
lean_dec_ref(v___y_4869_);
if (v_isShared_4896_ == 0)
{
v___x_4900_ = v___x_4895_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4893_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
else
{
lean_object* v_id_4902_; uint8_t v___x_4903_; 
v_id_4902_ = lean_ctor_get(v_a_4893_, 0);
v___x_4903_ = l_Lean_instBEqInternalExceptionId_beq(v___x_4880_, v_id_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4905_; 
lean_dec_ref(v___y_4869_);
if (v_isShared_4896_ == 0)
{
v___x_4905_ = v___x_4895_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4893_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_dec_ref_known(v_a_4893_, 2);
lean_del_object(v___x_4895_);
v___x_4907_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4908_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4907_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
lean_dec_ref(v___y_4869_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v_fst_4910_; lean_object* v_snd_4911_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
v_fst_4910_ = lean_ctor_get(v_a_4909_, 0);
lean_inc(v_fst_4910_);
v_snd_4911_ = lean_ctor_get(v_a_4909_, 1);
lean_inc(v_snd_4911_);
lean_dec(v_a_4909_);
v_fst_4858_ = v_fst_4910_;
v_snd_4859_ = v_snd_4911_;
goto v___jp_4857_;
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
v_a_4912_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4908_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4908_);
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
lean_object* v___x_4921_; 
lean_dec_ref(v___y_4869_);
if (v_isShared_4896_ == 0)
{
v___x_4921_ = v___x_4895_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4893_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
else
{
lean_object* v___x_4924_; 
lean_dec_ref(v___y_4869_);
if (v_isShared_4896_ == 0)
{
v___x_4924_ = v___x_4895_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4893_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
v___jp_4927_:
{
uint8_t v___x_4934_; 
v___x_4934_ = l_Lean_getPPAll(v___y_4928_);
if (v___x_4934_ == 0)
{
uint8_t v___x_4935_; 
v___x_4935_ = l_Lean_getPPAnalyze(v___y_4928_);
if (v___x_4935_ == 0)
{
v___y_4864_ = v___y_4928_;
v___y_4865_ = v_e_4929_;
v_optionsPerPos_4866_ = v_optionsPerPos_4850_;
v___y_4867_ = v___y_4930_;
v___y_4868_ = v___y_4931_;
v___y_4869_ = v___y_4932_;
v___y_4870_ = v___y_4933_;
goto v___jp_4863_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4850_) == 0)
{
v___y_4864_ = v___y_4928_;
v___y_4865_ = v_e_4929_;
v_optionsPerPos_4866_ = v_optionsPerPos_4850_;
v___y_4867_ = v___y_4930_;
v___y_4868_ = v___y_4931_;
v___y_4869_ = v___y_4932_;
v___y_4870_ = v___y_4933_;
goto v___jp_4863_;
}
else
{
lean_object* v___x_4936_; 
lean_inc_ref(v_e_4929_);
v___x_4936_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___y_4864_ = v___y_4928_;
v___y_4865_ = v_e_4929_;
v_optionsPerPos_4866_ = v_a_4937_;
v___y_4867_ = v___y_4930_;
v___y_4868_ = v___y_4931_;
v___y_4869_ = v___y_4932_;
v___y_4870_ = v___y_4933_;
goto v___jp_4863_;
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec_ref(v___y_4932_);
lean_dec_ref(v_e_4929_);
lean_dec_ref(v___y_4928_);
lean_dec_ref(v_delab_4851_);
v_a_4938_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4936_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4936_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
else
{
v___y_4864_ = v___y_4928_;
v___y_4865_ = v_e_4929_;
v_optionsPerPos_4866_ = v_optionsPerPos_4850_;
v___y_4867_ = v___y_4930_;
v___y_4868_ = v___y_4931_;
v___y_4869_ = v___y_4932_;
v___y_4870_ = v___y_4933_;
goto v___jp_4863_;
}
}
v___jp_4946_:
{
uint8_t v___x_4953_; 
v___x_4953_ = l_Lean_getPPBeta(v___y_4947_);
if (v___x_4953_ == 0)
{
v___y_4928_ = v___y_4947_;
v_e_4929_ = v_e_4948_;
v___y_4930_ = v___y_4949_;
v___y_4931_ = v___y_4950_;
v___y_4932_ = v___y_4951_;
v___y_4933_ = v___y_4952_;
goto v___jp_4927_;
}
else
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Lean_Core_betaReduce(v_e_4948_, v___y_4951_, v___y_4952_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v___y_4928_ = v___y_4947_;
v_e_4929_ = v_a_4955_;
v___y_4930_ = v___y_4949_;
v___y_4931_ = v___y_4950_;
v___y_4932_ = v___y_4951_;
v___y_4933_ = v___y_4952_;
goto v___jp_4927_;
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec_ref(v___y_4951_);
lean_dec_ref(v___y_4947_);
lean_dec_ref(v_delab_4851_);
lean_dec(v_optionsPerPos_4850_);
v_a_4956_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4954_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4954_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5112_, lean_object* v_optionsPerPos_5113_, lean_object* v_delab_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5112_, v_optionsPerPos_5113_, v_delab_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5121_, lean_object* v_e_5122_, lean_object* v_optionsPerPos_5123_, lean_object* v_delab_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v___x_5130_; 
v___x_5130_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5122_, v_optionsPerPos_5123_, v_delab_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5131_, lean_object* v_e_5132_, lean_object* v_optionsPerPos_5133_, lean_object* v_delab_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5131_, v_e_5132_, v_optionsPerPos_5133_, v_delab_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5142_, lean_object* v_optionsPerPos_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
v___x_5149_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5150_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5142_, v_optionsPerPos_5143_, v___x_5149_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5159_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5153_ = v___x_5150_;
v_isShared_5154_ = v_isSharedCheck_5159_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5150_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5159_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v_fst_5155_; lean_object* v___x_5157_; 
v_fst_5155_ = lean_ctor_get(v_a_5151_, 0);
lean_inc(v_fst_5155_);
lean_dec(v_a_5151_);
if (v_isShared_5154_ == 0)
{
lean_ctor_set(v___x_5153_, 0, v_fst_5155_);
v___x_5157_ = v___x_5153_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_fst_5155_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
else
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
v_a_5160_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5150_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5150_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5168_, lean_object* v_optionsPerPos_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_PrettyPrinter_delab(v_e_5168_, v_optionsPerPos_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5240_; uint8_t v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5240_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5241_ = 0;
v___x_5242_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5243_ = l_Lean_registerTraceClass(v___x_5240_, v___x_5241_, v___x_5242_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v___x_5244_; lean_object* v___x_5245_; 
lean_dec_ref_known(v___x_5243_, 1);
v___x_5244_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5245_ = l_Lean_registerTraceClass(v___x_5244_, v___x_5241_, v___x_5242_);
return v___x_5245_;
}
else
{
return v___x_5243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5246_){
_start:
{
lean_object* v_res_5247_; 
v_res_5247_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5247_;
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
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1967354858____hygCtx___hyg_2_();
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
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3808493988____hygCtx___hyg_2_();
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
