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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_getPPMaxSteps___boxed(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_getPPDeepTerms___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
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
uint8_t l_Lean_getPPMVarsLevels(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelIndex_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPMVarsLevels___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0;
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(124) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(457) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(479) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(470) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(470) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_44_);
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
else
{
lean_object* v_id_48_; uint8_t v___x_49_; 
v_id_48_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_id_48_);
lean_dec_ref(v_a_44_);
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
lean_dec_ref(v___x_43_);
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
lean_dec_ref(v_a_75_);
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
else
{
lean_object* v_id_79_; uint8_t v___x_80_; 
v_id_79_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_id_79_);
lean_dec_ref(v_a_75_);
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
lean_dec_ref(v___x_74_);
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
lean_object* v_optionsPerPos_233_; lean_object* v_currNamespace_234_; lean_object* v_openDecls_235_; uint8_t v_inPattern_236_; lean_object* v_subExpr_237_; lean_object* v_depth_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_247_; 
v_optionsPerPos_233_ = lean_ctor_get(v_ctx_226_, 0);
v_currNamespace_234_ = lean_ctor_get(v_ctx_226_, 1);
v_openDecls_235_ = lean_ctor_get(v_ctx_226_, 2);
v_inPattern_236_ = lean_ctor_get_uint8(v_ctx_226_, sizeof(void*)*5);
v_subExpr_237_ = lean_ctor_get(v_ctx_226_, 3);
v_depth_238_ = lean_ctor_get(v_ctx_226_, 4);
v_isSharedCheck_247_ = !lean_is_exclusive(v_ctx_226_);
if (v_isSharedCheck_247_ == 0)
{
v___x_240_ = v_ctx_226_;
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_depth_238_);
lean_inc(v_subExpr_237_);
lean_inc(v_openDecls_235_);
lean_inc(v_currNamespace_234_);
lean_inc(v_optionsPerPos_233_);
lean_dec(v_ctx_226_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_apply_1(v_f_224_, v_subExpr_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_optionsPerPos_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_currNamespace_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_openDecls_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_depth_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*5, v_inPattern_236_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v___y_227_);
v___x_245_ = lean_apply_7(v_x_225_, v___x_244_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, lean_box(0));
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object* v_00_u03b1_248_, lean_object* v_f_249_, lean_object* v_x_250_, lean_object* v_ctx_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(v_00_u03b1_248_, v_f_249_, v_x_250_, v_ctx_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; lean_object* v_holeIter_269_; lean_object* v___x_270_; 
v___x_268_ = lean_st_ref_get(v___y_262_);
v_holeIter_269_ = lean_ctor_get(v___x_268_, 2);
lean_inc_ref(v_holeIter_269_);
lean_dec(v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_holeIter_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object* v_iter_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_steps_288_; lean_object* v_infos_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v___x_287_ = lean_st_ref_take(v___y_281_);
v_steps_288_ = lean_ctor_get(v___x_287_, 0);
v_infos_289_ = lean_ctor_get(v___x_287_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_287_, 2);
lean_dec(v_unused_300_);
v___x_291_ = v___x_287_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_infos_289_);
lean_inc(v_steps_288_);
lean_dec(v___x_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 2, v_iter_279_);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_steps_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_infos_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_iter_279_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_st_ref_set(v___y_281_, v___x_294_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object* v_iter_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(v_iter_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object* v_00_u03b1_310_, lean_object* v_f_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; lean_object* v_steps_320_; lean_object* v_infos_321_; lean_object* v_holeIter_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_334_; 
v___x_319_ = lean_st_ref_take(v___y_313_);
v_steps_320_ = lean_ctor_get(v___x_319_, 0);
v_infos_321_ = lean_ctor_get(v___x_319_, 1);
v_holeIter_322_ = lean_ctor_get(v___x_319_, 2);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_334_ == 0)
{
v___x_324_ = v___x_319_;
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_holeIter_322_);
lean_inc(v_infos_321_);
lean_inc(v_steps_320_);
lean_dec(v___x_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_330_; 
v___x_326_ = lean_apply_1(v_f_311_, v_holeIter_322_);
v_fst_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v___x_326_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 2, v_snd_328_);
v___x_330_ = v___x_324_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_steps_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_infos_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_snd_328_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_st_ref_set(v___y_313_, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_fst_327_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object* v_00_u03b1_335_, lean_object* v_f_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(v_00_u03b1_335_, v_f_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_builtin_353_, lean_object* v_declName_354_, lean_object* v_key_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_builtin_361_, lean_object* v_declName_362_, lean_object* v_key_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v_builtin_boxed_367_; lean_object* v_res_368_; 
v_builtin_boxed_367_ = lean_unbox(v_builtin_361_);
v_res_368_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_builtin_boxed_367_, v_declName_362_, v_key_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v_key_363_);
lean_dec(v_declName_362_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_369_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
lean_ctor_set(v___x_374_, 3, v___x_373_);
lean_ctor_set(v___x_374_, 4, v___x_372_);
lean_ctor_set(v___x_374_, 5, v___x_372_);
lean_ctor_set(v___x_374_, 6, v___x_372_);
lean_ctor_set(v___x_374_, 7, v___x_372_);
lean_ctor_set(v___x_374_, 8, v___x_372_);
lean_ctor_set(v___x_374_, 9, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(32u);
v___x_376_ = lean_mk_empty_array_with_capacity(v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_378_ = ((size_t)5ULL);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_unsigned_to_nat(32u);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
v___x_382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_383_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_379_);
lean_ctor_set(v___x_383_, 3, v___x_379_);
lean_ctor_set_usize(v___x_383_, 4, v___x_378_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_box(1);
v___x_385_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_384_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_409_, lean_object* v_declHint_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_env_414_; uint8_t v___x_415_; 
v___x_413_ = lean_st_ref_get(v___y_411_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_413_);
v___x_415_ = l_Lean_Name_isAnonymous(v_declHint_410_);
if (v___x_415_ == 0)
{
uint8_t v_isExporting_416_; 
v_isExporting_416_ = lean_ctor_get_uint8(v_env_414_, sizeof(void*)*8);
if (v_isExporting_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec_ref(v_env_414_);
lean_dec(v_declHint_410_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_msg_409_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; uint8_t v___x_419_; 
lean_inc_ref(v_env_414_);
v___x_418_ = l_Lean_Environment_setExporting(v_env_414_, v___x_415_);
lean_inc(v_declHint_410_);
lean_inc_ref(v___x_418_);
v___x_419_ = l_Lean_Environment_contains(v___x_418_, v_declHint_410_, v_isExporting_416_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v___x_418_);
lean_dec_ref(v_env_414_);
lean_dec(v_declHint_410_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_msg_409_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_c_426_; lean_object* v___x_427_; 
v___x_421_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_423_ = l_Lean_Options_empty;
v___x_424_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_424_, 0, v___x_418_);
lean_ctor_set(v___x_424_, 1, v___x_421_);
lean_ctor_set(v___x_424_, 2, v___x_422_);
lean_ctor_set(v___x_424_, 3, v___x_423_);
lean_inc(v_declHint_410_);
v___x_425_ = l_Lean_MessageData_ofConstName(v_declHint_410_, v___x_415_);
v_c_426_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_426_, 0, v___x_424_);
lean_ctor_set(v_c_426_, 1, v___x_425_);
v___x_427_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_414_, v_declHint_410_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v_env_414_);
lean_dec(v_declHint_410_);
v___x_428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_c_426_);
v___x_430_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_MessageData_note(v___x_431_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v_msg_409_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_470_; 
v_val_435_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_470_ == 0)
{
v___x_437_ = v___x_427_;
v_isShared_438_ = v_isSharedCheck_470_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v___x_427_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_470_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_mod_442_; uint8_t v___x_443_; 
v___x_439_ = lean_box(0);
v___x_440_ = l_Lean_Environment_header(v_env_414_);
lean_dec_ref(v_env_414_);
v___x_441_ = l_Lean_EnvironmentHeader_moduleNames(v___x_440_);
v_mod_442_ = lean_array_get(v___x_439_, v___x_441_, v_val_435_);
lean_dec(v_val_435_);
lean_dec_ref(v___x_441_);
v___x_443_ = l_Lean_isPrivateName(v_declHint_410_);
lean_dec(v_declHint_410_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_c_426_);
v___x_446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_MessageData_ofName(v_mod_442_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_MessageData_note(v___x_451_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v_msg_409_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 0);
lean_ctor_set(v___x_437_, 0, v___x_453_);
v___x_455_ = v___x_437_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_c_426_);
v___x_459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_MessageData_ofName(v_mod_442_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_MessageData_note(v___x_464_);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v_msg_409_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 0);
lean_ctor_set(v___x_437_, 0, v___x_466_);
v___x_468_ = v___x_437_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec_ref(v_env_414_);
lean_dec(v_declHint_410_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_msg_409_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_472_, lean_object* v_declHint_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_472_, v_declHint_473_, v___y_474_);
lean_dec(v___y_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(lean_object* v_msg_477_, lean_object* v_declHint_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_492_; 
v___x_482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_477_, v_declHint_478_, v___y_480_);
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = l_Lean_unknownIdentifierMessageTag;
v___x_488_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_493_, lean_object* v_declHint_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(v_msg_493_, v_declHint_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_msgData_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; lean_object* v_options_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_503_ = lean_st_ref_get(v___y_501_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v_options_505_ = lean_ctor_get(v___y_500_, 2);
v___x_506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_507_ = lean_unsigned_to_nat(32u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
lean_dec_ref(v___x_508_);
v___x_509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
lean_inc_ref(v_options_505_);
v___x_510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_510_, 0, v_env_504_);
lean_ctor_set(v___x_510_, 1, v___x_506_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
lean_ctor_set(v___x_510_, 3, v_options_505_);
v___x_511_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_msgData_499_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msgData_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_ref_522_; lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_ref_522_ = lean_ctor_get(v___y_519_, 5);
v___x_523_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msg_518_, v___y_519_, v___y_520_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
lean_inc(v_ref_522_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_ref_522_);
lean_ctor_set(v___x_528_, 1, v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 1);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg___boxed(lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_fileName_543_; lean_object* v_fileMap_544_; lean_object* v_options_545_; lean_object* v_currRecDepth_546_; lean_object* v_maxRecDepth_547_; lean_object* v_ref_548_; lean_object* v_currNamespace_549_; lean_object* v_openDecls_550_; lean_object* v_initHeartbeats_551_; lean_object* v_maxHeartbeats_552_; lean_object* v_quotContext_553_; lean_object* v_currMacroScope_554_; uint8_t v_diag_555_; lean_object* v_cancelTk_x3f_556_; uint8_t v_suppressElabErrors_557_; lean_object* v_inheritedTraceOptions_558_; lean_object* v_ref_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_fileName_543_ = lean_ctor_get(v___y_540_, 0);
v_fileMap_544_ = lean_ctor_get(v___y_540_, 1);
v_options_545_ = lean_ctor_get(v___y_540_, 2);
v_currRecDepth_546_ = lean_ctor_get(v___y_540_, 3);
v_maxRecDepth_547_ = lean_ctor_get(v___y_540_, 4);
v_ref_548_ = lean_ctor_get(v___y_540_, 5);
v_currNamespace_549_ = lean_ctor_get(v___y_540_, 6);
v_openDecls_550_ = lean_ctor_get(v___y_540_, 7);
v_initHeartbeats_551_ = lean_ctor_get(v___y_540_, 8);
v_maxHeartbeats_552_ = lean_ctor_get(v___y_540_, 9);
v_quotContext_553_ = lean_ctor_get(v___y_540_, 10);
v_currMacroScope_554_ = lean_ctor_get(v___y_540_, 11);
v_diag_555_ = lean_ctor_get_uint8(v___y_540_, sizeof(void*)*14);
v_cancelTk_x3f_556_ = lean_ctor_get(v___y_540_, 12);
v_suppressElabErrors_557_ = lean_ctor_get_uint8(v___y_540_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_558_ = lean_ctor_get(v___y_540_, 13);
v_ref_559_ = l_Lean_replaceRef(v_ref_538_, v_ref_548_);
lean_inc_ref(v_inheritedTraceOptions_558_);
lean_inc(v_cancelTk_x3f_556_);
lean_inc(v_currMacroScope_554_);
lean_inc(v_quotContext_553_);
lean_inc(v_maxHeartbeats_552_);
lean_inc(v_initHeartbeats_551_);
lean_inc(v_openDecls_550_);
lean_inc(v_currNamespace_549_);
lean_inc(v_maxRecDepth_547_);
lean_inc(v_currRecDepth_546_);
lean_inc_ref(v_options_545_);
lean_inc_ref(v_fileMap_544_);
lean_inc_ref(v_fileName_543_);
v___x_560_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_560_, 0, v_fileName_543_);
lean_ctor_set(v___x_560_, 1, v_fileMap_544_);
lean_ctor_set(v___x_560_, 2, v_options_545_);
lean_ctor_set(v___x_560_, 3, v_currRecDepth_546_);
lean_ctor_set(v___x_560_, 4, v_maxRecDepth_547_);
lean_ctor_set(v___x_560_, 5, v_ref_559_);
lean_ctor_set(v___x_560_, 6, v_currNamespace_549_);
lean_ctor_set(v___x_560_, 7, v_openDecls_550_);
lean_ctor_set(v___x_560_, 8, v_initHeartbeats_551_);
lean_ctor_set(v___x_560_, 9, v_maxHeartbeats_552_);
lean_ctor_set(v___x_560_, 10, v_quotContext_553_);
lean_ctor_set(v___x_560_, 11, v_currMacroScope_554_);
lean_ctor_set(v___x_560_, 12, v_cancelTk_x3f_556_);
lean_ctor_set(v___x_560_, 13, v_inheritedTraceOptions_558_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*14, v_diag_555_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*14 + 1, v_suppressElabErrors_557_);
v___x_561_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_539_, v___x_560_, v___y_541_);
lean_dec_ref(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_562_, v_msg_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_ref_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18(v_msg_569_, v_declHint_570_, v___y_571_, v___y_572_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_568_, v_a_575_, v___y_571_, v___y_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_ref_577_, lean_object* v_msg_578_, lean_object* v_declHint_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_577_, v_msg_578_, v_declHint_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_ref_577_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(lean_object* v_ref_590_, lean_object* v_constName_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__1);
v___x_596_ = 0;
lean_inc(v_constName_591_);
v___x_597_ = l_Lean_MessageData_ofConstName(v_constName_591_, v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_590_, v___x_600_, v_constName_591_, v___y_592_, v___y_593_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___boxed(lean_object* v_ref_602_, lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_602_, v_constName_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v_ref_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(lean_object* v_constName_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_ref_612_; lean_object* v___x_613_; 
v_ref_612_ = lean_ctor_get(v___y_609_, 5);
v___x_613_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_612_, v_constName_608_, v___y_609_, v___y_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_constName_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_constName_619_, lean_object* v___y_620_, lean_object* v___y_621_){
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
v___x_627_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_619_, v___y_620_, v___y_621_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_constName_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_constName_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object* v_a_641_, lean_object* v_a_642_){
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v_constName_655_);
v___x_659_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_constName_655_, v___y_656_, v___y_657_);
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
v___x_666_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_levelParams_664_, v___x_665_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_constName_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_constName_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(lean_object* v_t_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_infoState_689_; uint8_t v_enabled_690_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_infoState_689_ = lean_ctor_get(v___x_688_, 7);
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
lean_object* v___x_693_; lean_object* v_infoState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_traceState_699_; lean_object* v_cache_700_; lean_object* v_messages_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_724_; 
v___x_693_ = lean_st_ref_take(v___y_686_);
v_infoState_694_ = lean_ctor_get(v___x_693_, 7);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_traceState_699_ = lean_ctor_get(v___x_693_, 4);
v_cache_700_ = lean_ctor_get(v___x_693_, 5);
v_messages_701_ = lean_ctor_get(v___x_693_, 6);
v_snapshotTasks_702_ = lean_ctor_get(v___x_693_, 8);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_724_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_701_);
lean_inc(v_cache_700_);
lean_inc(v_traceState_699_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v_enabled_706_; lean_object* v_assignment_707_; lean_object* v_lazyAssignment_708_; lean_object* v_trees_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_enabled_706_ = lean_ctor_get_uint8(v_infoState_694_, sizeof(void*)*3);
v_assignment_707_ = lean_ctor_get(v_infoState_694_, 0);
v_lazyAssignment_708_ = lean_ctor_get(v_infoState_694_, 1);
v_trees_709_ = lean_ctor_get(v_infoState_694_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_infoState_694_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_infoState_694_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_trees_709_);
lean_inc(v_lazyAssignment_708_);
lean_inc(v_assignment_707_);
lean_dec(v_infoState_694_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_trees_709_, v_t_685_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_lazyAssignment_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*3, v_enabled_706_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 7, v___x_715_);
v___x_717_ = v___x_704_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_traceState_699_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_cache_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_messages_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v_snapshotTasks_702_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_st_ref_set(v___y_686_, v___x_717_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v_t_725_, v___y_726_);
lean_dec(v___y_726_);
return v_res_728_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(32u);
v___x_730_ = lean_mk_empty_array_with_capacity(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((size_t)5ULL);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_unsigned_to_nat(32u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0);
v___x_737_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_733_);
lean_ctor_set(v___x_737_, 3, v___x_733_);
lean_ctor_set_usize(v___x_737_, 4, v___x_732_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_t_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_infoState_743_; uint8_t v_enabled_744_; 
v___x_742_ = lean_st_ref_get(v___y_740_);
v_infoState_743_ = lean_ctor_get(v___x_742_, 7);
lean_inc_ref(v_infoState_743_);
lean_dec(v___x_742_);
v_enabled_744_ = lean_ctor_get_uint8(v_infoState_743_, sizeof(void*)*3);
lean_dec_ref(v_infoState_743_);
if (v_enabled_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v_t_738_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1);
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v_t_738_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v___x_748_, v___y_740_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_t_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v_t_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(lean_object* v_stx_755_, lean_object* v_n_756_, lean_object* v_expectedType_x3f_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_n_756_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v_stx_755_);
v___x_765_ = l_Lean_LocalContext_empty;
v___x_766_ = 0;
v___x_767_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v_expectedType_x3f_757_);
lean_ctor_set(v___x_767_, 3, v_a_762_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*4, v___x_766_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*4 + 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v___x_768_, v___y_758_, v___y_759_);
return v___x_769_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_expectedType_x3f_757_);
lean_dec(v_stx_755_);
v_a_770_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_761_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_761_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_778_, lean_object* v_n_779_, lean_object* v_expectedType_x3f_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_stx_778_, v_n_779_, v_expectedType_x3f_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v_key_788_; lean_object* v_value_789_; lean_object* v_tail_790_; uint8_t v___x_791_; 
v_key_788_ = lean_ctor_get(v_x_786_, 0);
v_value_789_ = lean_ctor_get(v_x_786_, 1);
v_tail_790_ = lean_ctor_get(v_x_786_, 2);
v___x_791_ = lean_name_eq(v_key_788_, v_a_785_);
if (v___x_791_ == 0)
{
v_x_786_ = v_tail_790_;
goto _start;
}
else
{
lean_object* v___x_793_; 
lean_inc(v_value_789_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_value_789_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_794_, v_x_795_);
lean_dec(v_x_795_);
lean_dec(v_a_794_);
return v_res_796_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_797_; uint64_t v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1723u);
v___x_798_ = lean_uint64_of_nat(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_buckets_801_; lean_object* v___x_802_; uint64_t v___y_804_; 
v_buckets_801_ = lean_ctor_get(v_m_799_, 1);
v___x_802_ = lean_array_get_size(v_buckets_801_);
if (lean_obj_tag(v_a_800_) == 0)
{
uint64_t v___x_818_; 
v___x_818_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0);
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
v___x_817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_800_, v___x_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_m_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_m_820_);
return v_res_822_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_823_; double v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_float_of_nat(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_cls_828_, lean_object* v_msg_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_ref_833_; lean_object* v___x_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_879_; 
v_ref_833_ = lean_ctor_get(v___y_830_, 5);
v___x_834_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_msg_829_, v___y_830_, v___y_831_);
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_879_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_879_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_879_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_traceState_840_; lean_object* v_env_841_; lean_object* v_nextMacroScope_842_; lean_object* v_ngen_843_; lean_object* v_auxDeclNGen_844_; lean_object* v_cache_845_; lean_object* v_messages_846_; lean_object* v_infoState_847_; lean_object* v_snapshotTasks_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_878_; 
v___x_839_ = lean_st_ref_take(v___y_831_);
v_traceState_840_ = lean_ctor_get(v___x_839_, 4);
v_env_841_ = lean_ctor_get(v___x_839_, 0);
v_nextMacroScope_842_ = lean_ctor_get(v___x_839_, 1);
v_ngen_843_ = lean_ctor_get(v___x_839_, 2);
v_auxDeclNGen_844_ = lean_ctor_get(v___x_839_, 3);
v_cache_845_ = lean_ctor_get(v___x_839_, 5);
v_messages_846_ = lean_ctor_get(v___x_839_, 6);
v_infoState_847_ = lean_ctor_get(v___x_839_, 7);
v_snapshotTasks_848_ = lean_ctor_get(v___x_839_, 8);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_878_ == 0)
{
v___x_850_ = v___x_839_;
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snapshotTasks_848_);
lean_inc(v_infoState_847_);
lean_inc(v_messages_846_);
lean_inc(v_cache_845_);
lean_inc(v_traceState_840_);
lean_inc(v_auxDeclNGen_844_);
lean_inc(v_ngen_843_);
lean_inc(v_nextMacroScope_842_);
lean_inc(v_env_841_);
lean_dec(v___x_839_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint64_t v_tid_852_; lean_object* v_traces_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_877_; 
v_tid_852_ = lean_ctor_get_uint64(v_traceState_840_, sizeof(void*)*1);
v_traces_853_ = lean_ctor_get(v_traceState_840_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_traceState_840_);
if (v_isSharedCheck_877_ == 0)
{
v___x_855_ = v_traceState_840_;
v_isShared_856_ = v_isSharedCheck_877_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_traces_853_);
lean_dec(v_traceState_840_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_877_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; double v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0);
v___x_859_ = 0;
v___x_860_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_861_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_861_, 0, v_cls_828_);
lean_ctor_set(v___x_861_, 1, v___x_857_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
lean_ctor_set_float(v___x_861_, sizeof(void*)*3, v___x_858_);
lean_ctor_set_float(v___x_861_, sizeof(void*)*3 + 8, v___x_858_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3 + 16, v___x_859_);
v___x_862_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2));
v___x_863_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v_a_835_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
lean_inc(v_ref_833_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_ref_833_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_PersistentArray_push___redArg(v_traces_853_, v___x_864_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_865_);
v___x_867_ = v___x_855_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_865_);
lean_ctor_set_uint64(v_reuseFailAlloc_876_, sizeof(void*)*1, v_tid_852_);
v___x_867_ = v_reuseFailAlloc_876_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v___x_867_);
v___x_869_ = v___x_850_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_env_841_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_nextMacroScope_842_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_ngen_843_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_auxDeclNGen_844_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_cache_845_);
lean_ctor_set(v_reuseFailAlloc_875_, 6, v_messages_846_);
lean_ctor_set(v_reuseFailAlloc_875_, 7, v_infoState_847_);
lean_ctor_set(v_reuseFailAlloc_875_, 8, v_snapshotTasks_848_);
v___x_869_ = v_reuseFailAlloc_875_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_870_ = lean_st_ref_set(v___y_831_, v___x_869_);
v___x_871_ = lean_box(0);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_871_);
v___x_873_ = v___x_837_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_cls_880_, lean_object* v_msg_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_cls_880_, v_msg_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_886_, lean_object* v_i_887_, lean_object* v_k_888_){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_get_size(v_keys_886_);
v___x_890_ = lean_nat_dec_lt(v_i_887_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec(v_i_887_);
return v___x_890_;
}
else
{
lean_object* v_k_x27_891_; uint8_t v___x_892_; 
v_k_x27_891_ = lean_array_fget_borrowed(v_keys_886_, v_i_887_);
v___x_892_ = l_Lean_instBEqExtraModUse_beq(v_k_888_, v_k_x27_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_i_887_, v___x_893_);
lean_dec(v_i_887_);
v_i_887_ = v___x_894_;
goto _start;
}
else
{
lean_dec(v_i_887_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_896_, lean_object* v_i_897_, lean_object* v_k_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_896_, v_i_897_, v_k_898_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v_keys_896_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; 
v___x_901_ = ((size_t)5ULL);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_shift_left(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; 
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_906_ = lean_usize_sub(v___x_905_, v___x_904_);
return v___x_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v_es_910_; lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_j_915_; lean_object* v___x_916_; 
v_es_910_ = lean_ctor_get(v_x_907_, 0);
v___x_911_ = lean_box(2);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_914_ = lean_usize_land(v_x_908_, v___x_913_);
v_j_915_ = lean_usize_to_nat(v___x_914_);
v___x_916_ = lean_array_get_borrowed(v___x_911_, v_es_910_, v_j_915_);
lean_dec(v_j_915_);
switch(lean_obj_tag(v___x_916_))
{
case 0:
{
lean_object* v_key_917_; uint8_t v___x_918_; 
v_key_917_ = lean_ctor_get(v___x_916_, 0);
v___x_918_ = l_Lean_instBEqExtraModUse_beq(v_x_909_, v_key_917_);
return v___x_918_;
}
case 1:
{
lean_object* v_node_919_; size_t v___x_920_; 
v_node_919_ = lean_ctor_get(v___x_916_, 0);
v___x_920_ = lean_usize_shift_right(v_x_908_, v___x_912_);
v_x_907_ = v_node_919_;
v_x_908_ = v___x_920_;
goto _start;
}
default: 
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
else
{
lean_object* v_ks_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_ks_923_ = lean_ctor_get(v_x_907_, 0);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_923_, v___x_924_, v_x_909_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
size_t v_x_7999__boxed_929_; uint8_t v_res_930_; lean_object* v_r_931_; 
v_x_7999__boxed_929_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_res_930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_926_, v_x_7999__boxed_929_, v_x_928_);
lean_dec_ref(v_x_928_);
lean_dec_ref(v_x_926_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
uint64_t v___x_934_; size_t v___x_935_; uint8_t v___x_936_; 
v___x_934_ = l_Lean_instHashableExtraModUse_hash(v_x_933_);
v___x_935_ = lean_uint64_to_usize(v___x_934_);
v___x_936_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_932_, v___x_935_, v_x_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_937_, v_x_938_);
lean_dec_ref(v_x_938_);
lean_dec_ref(v_x_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_944_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_945_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_946_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_cls_965_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7));
v___x_966_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_967_ = l_Lean_Name_append(v___x_966_, v_cls_965_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_mod_978_, uint8_t v_isMeta_979_, lean_object* v_hint_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_env_985_; uint8_t v_isExporting_986_; lean_object* v___x_987_; lean_object* v_env_988_; lean_object* v___x_989_; lean_object* v_entry_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___y_995_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_984_ = lean_st_ref_get(v___y_982_);
v_env_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_env_985_);
lean_dec(v___x_984_);
v_isExporting_986_ = lean_ctor_get_uint8(v_env_985_, sizeof(void*)*8);
lean_dec_ref(v_env_985_);
v___x_987_ = lean_st_ref_get(v___y_982_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2);
lean_inc(v_mod_978_);
v_entry_990_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_990_, 0, v_mod_978_);
lean_ctor_set_uint8(v_entry_990_, sizeof(void*)*1, v_isExporting_986_);
lean_ctor_set_uint8(v_entry_990_, sizeof(void*)*1 + 1, v_isMeta_979_);
v___x_991_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_992_ = lean_box(1);
v___x_993_ = lean_box(0);
v___x_1020_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_989_, v___x_991_, v_env_988_, v___x_992_, v___x_993_);
v___x_1021_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_1020_, v_entry_990_);
lean_dec(v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v_options_1022_; uint8_t v_hasTrace_1023_; 
v_options_1022_ = lean_ctor_get(v___y_981_, 2);
v_hasTrace_1023_ = lean_ctor_get_uint8(v_options_1022_, sizeof(void*)*1);
if (v_hasTrace_1023_ == 0)
{
lean_dec(v_hint_980_);
lean_dec(v_mod_978_);
v___y_995_ = v___y_982_;
goto v___jp_994_;
}
else
{
lean_object* v_inheritedTraceOptions_1024_; lean_object* v_cls_1025_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_inheritedTraceOptions_1024_ = lean_ctor_get(v___y_981_, 13);
v_cls_1025_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7));
v___x_1045_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15);
v___x_1046_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1024_, v_options_1022_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec(v_hint_980_);
lean_dec(v_mod_978_);
v___y_995_ = v___y_982_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1047_; lean_object* v___y_1049_; 
v___x_1047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17);
if (v_isExporting_986_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__22));
v___y_1049_ = v___x_1056_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__23));
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
v___jp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_inc_ref(v___y_1049_);
v___x_1050_ = l_Lean_stringToMessageData(v___y_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1047_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
if (v_isMeta_979_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20));
v___y_1032_ = v___x_1053_;
v___y_1033_ = v___x_1054_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__21));
v___y_1032_ = v___x_1053_;
v___y_1033_ = v___x_1055_;
goto v___jp_1031_;
}
}
}
v___jp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1027_);
lean_ctor_set(v___x_1029_, 1, v___y_1028_);
v___x_1030_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_cls_1025_, v___x_1029_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_dec_ref(v___x_1030_);
v___y_995_ = v___y_982_;
goto v___jp_994_;
}
else
{
lean_dec_ref(v_entry_990_);
return v___x_1030_;
}
}
v___jp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
lean_inc_ref(v___y_1033_);
v___x_1034_ = l_Lean_stringToMessageData(v___y_1033_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_1032_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_ofName(v_mod_978_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_Name_isAnonymous(v_hint_980_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11);
v___x_1042_ = l_Lean_MessageData_ofName(v_hint_980_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___y_1027_ = v___x_1039_;
v___y_1028_ = v___x_1043_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1044_; 
lean_dec(v_hint_980_);
v___x_1044_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12);
v___y_1027_ = v___x_1039_;
v___y_1028_ = v___x_1044_;
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v_entry_990_);
lean_dec(v_hint_980_);
lean_dec(v_mod_978_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v_toEnvExtension_997_; lean_object* v_env_998_; lean_object* v_nextMacroScope_999_; lean_object* v_ngen_1000_; lean_object* v_auxDeclNGen_1001_; lean_object* v_traceState_1002_; lean_object* v_messages_1003_; lean_object* v_infoState_1004_; lean_object* v_snapshotTasks_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v___x_996_ = lean_st_ref_take(v___y_995_);
v_toEnvExtension_997_ = lean_ctor_get(v___x_991_, 0);
v_env_998_ = lean_ctor_get(v___x_996_, 0);
v_nextMacroScope_999_ = lean_ctor_get(v___x_996_, 1);
v_ngen_1000_ = lean_ctor_get(v___x_996_, 2);
v_auxDeclNGen_1001_ = lean_ctor_get(v___x_996_, 3);
v_traceState_1002_ = lean_ctor_get(v___x_996_, 4);
v_messages_1003_ = lean_ctor_get(v___x_996_, 6);
v_infoState_1004_ = lean_ctor_get(v___x_996_, 7);
v_snapshotTasks_1005_ = lean_ctor_get(v___x_996_, 8);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_996_, 5);
lean_dec(v_unused_1019_);
v___x_1007_ = v___x_996_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snapshotTasks_1005_);
lean_inc(v_infoState_1004_);
lean_inc(v_messages_1003_);
lean_inc(v_traceState_1002_);
lean_inc(v_auxDeclNGen_1001_);
lean_inc(v_ngen_1000_);
lean_inc(v_nextMacroScope_999_);
lean_inc(v_env_998_);
lean_dec(v___x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_asyncMode_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v_asyncMode_1009_ = lean_ctor_get(v_toEnvExtension_997_, 2);
v___x_1010_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_991_, v_env_998_, v_entry_990_, v_asyncMode_1009_, v___x_993_);
v___x_1011_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 5, v___x_1011_);
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1013_ = v___x_1007_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_nextMacroScope_999_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_ngen_1000_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_auxDeclNGen_1001_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_traceState_1002_);
lean_ctor_set(v_reuseFailAlloc_1017_, 5, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1017_, 6, v_messages_1003_);
lean_ctor_set(v_reuseFailAlloc_1017_, 7, v_infoState_1004_);
lean_ctor_set(v_reuseFailAlloc_1017_, 8, v_snapshotTasks_1005_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_st_ref_set(v___y_995_, v___x_1013_);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_mod_1060_, lean_object* v_isMeta_1061_, lean_object* v_hint_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_isMeta_boxed_1066_; lean_object* v_res_1067_; 
v_isMeta_boxed_1066_ = lean_unbox(v_isMeta_1061_);
v_res_1067_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_mod_1060_, v_isMeta_boxed_1066_, v_hint_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(lean_object* v___x_1068_, lean_object* v_declName_1069_, lean_object* v_as_1070_, size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_lt(v_i_1072_, v_sz_1071_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec(v_declName_1069_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_b_1073_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v_modules_1080_; lean_object* v___x_1081_; lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v_toImport_1084_; lean_object* v_module_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1079_ = l_Lean_Environment_header(v___x_1068_);
v_modules_1080_ = lean_ctor_get(v___x_1079_, 3);
lean_inc_ref(v_modules_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1082_ = lean_array_uget_borrowed(v_as_1070_, v_i_1072_);
v___x_1083_ = lean_array_get(v___x_1081_, v_modules_1080_, v_a_1082_);
lean_dec_ref(v_modules_1080_);
v_toImport_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_toImport_1084_);
lean_dec(v___x_1083_);
v_module_1085_ = lean_ctor_get(v_toImport_1084_, 0);
lean_inc(v_module_1085_);
lean_dec_ref(v_toImport_1084_);
v___x_1086_ = 0;
lean_inc(v_declName_1069_);
v___x_1087_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_1085_, v___x_1086_, v_declName_1069_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; 
lean_dec_ref(v___x_1087_);
v___x_1088_ = lean_box(0);
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1072_, v___x_1089_);
v_i_1072_ = v___x_1090_;
v_b_1073_ = v___x_1088_;
goto _start;
}
else
{
lean_dec(v_declName_1069_);
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v___x_1092_, lean_object* v_declName_1093_, lean_object* v_as_1094_, lean_object* v_sz_1095_, lean_object* v_i_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
size_t v_sz_boxed_1101_; size_t v_i_boxed_1102_; lean_object* v_res_1103_; 
v_sz_boxed_1101_ = lean_unbox_usize(v_sz_1095_);
lean_dec(v_sz_1095_);
v_i_boxed_1102_ = lean_unbox_usize(v_i_1096_);
lean_dec(v_i_1096_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v___x_1092_, v_declName_1093_, v_as_1094_, v_sz_boxed_1101_, v_i_boxed_1102_, v_b_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_as_1094_);
lean_dec_ref(v___x_1092_);
return v_res_1103_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1));
v___x_1107_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0));
v___x_1108_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(lean_object* v_declName_1111_, uint8_t v_isMeta_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_env_1120_; lean_object* v___y_1122_; lean_object* v___x_1135_; 
v___x_1116_ = lean_st_ref_get(v___y_1114_);
v_env_1120_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_env_1120_);
lean_dec(v___x_1116_);
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1120_, v_declName_1111_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref(v_env_1120_);
lean_dec(v_declName_1111_);
goto v___jp_1117_;
}
else
{
lean_object* v_val_1136_; lean_object* v___x_1137_; lean_object* v_modules_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_val_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref(v___x_1135_);
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
lean_dec(v_declName_1111_);
goto v___jp_1117_;
}
else
{
lean_object* v___x_1141_; lean_object* v_env_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___y_1146_; 
v___x_1141_ = lean_st_ref_get(v___y_1114_);
v_env_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_env_1142_);
lean_dec(v___x_1141_);
v___x_1143_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2);
v___x_1144_ = lean_array_fget(v_modules_1138_, v_val_1136_);
lean_dec(v_val_1136_);
lean_dec_ref(v_modules_1138_);
if (v_isMeta_1112_ == 0)
{
lean_dec_ref(v_env_1142_);
v___y_1146_ = v_isMeta_1112_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1157_; 
lean_inc(v_declName_1111_);
v___x_1157_ = l_Lean_isMarkedMeta(v_env_1142_, v_declName_1111_);
if (v___x_1157_ == 0)
{
v___y_1146_ = v_isMeta_1112_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = 0;
v___y_1146_ = v___x_1158_;
goto v___jp_1145_;
}
}
v___jp_1145_:
{
lean_object* v_toImport_1147_; lean_object* v_module_1148_; lean_object* v___x_1149_; 
v_toImport_1147_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_toImport_1147_);
lean_dec(v___x_1144_);
v_module_1148_ = lean_ctor_get(v_toImport_1147_, 0);
lean_inc(v_module_1148_);
lean_dec_ref(v_toImport_1147_);
lean_inc(v_declName_1111_);
v___x_1149_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_1148_, v___y_1146_, v_declName_1111_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v___x_1149_);
v___x_1150_ = l_Lean_indirectModUseExt;
v___x_1151_ = lean_box(1);
v___x_1152_ = lean_box(0);
lean_inc_ref(v_env_1120_);
v___x_1153_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1143_, v___x_1150_, v_env_1120_, v___x_1151_, v___x_1152_);
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_1153_, v_declName_1111_);
lean_dec(v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3));
v___y_1122_ = v___x_1155_;
goto v___jp_1121_;
}
else
{
lean_object* v_val_1156_; 
v_val_1156_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_val_1156_);
lean_dec_ref(v___x_1154_);
v___y_1122_ = v_val_1156_;
goto v___jp_1121_;
}
}
else
{
lean_dec_ref(v_env_1120_);
lean_dec(v_declName_1111_);
return v___x_1149_;
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
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v_env_1120_, v_declName_1111_, v___y_1122_, v_sz_1124_, v___x_1125_, v___x_1123_, v___y_1113_, v___y_1114_);
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
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___boxed(lean_object* v_declName_1159_, lean_object* v_isMeta_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_isMeta_boxed_1164_; lean_object* v_res_1165_; 
v_isMeta_boxed_1164_ = lean_unbox(v_isMeta_1160_);
v_res_1165_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_declName_1159_, v_isMeta_boxed_1164_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_x_1169_, lean_object* v_stx_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1228_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1228_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1228_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v_infoState_1180_; uint8_t v_enabled_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_st_ref_get(v___y_1172_);
v_infoState_1180_ = lean_ctor_get(v___x_1179_, 7);
lean_inc_ref(v_infoState_1180_);
lean_dec(v___x_1179_);
v_enabled_1181_ = lean_ctor_get_uint8(v_infoState_1180_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1180_);
v___x_1182_ = l_Lean_Syntax_getId(v_a_1175_);
if (v_enabled_1181_ == 0)
{
lean_object* v___x_1184_; 
lean_dec(v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1182_);
v___x_1184_ = v___x_1177_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = l_Lean_Name_getRoot(v___x_1182_);
v___x_1187_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1188_ = lean_name_eq(v___x_1186_, v___x_1187_);
lean_dec(v___x_1186_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
lean_dec(v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1182_);
v___x_1190_ = v___x_1177_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1182_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1192_ = lean_st_ref_get(v___y_1172_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_box(0);
lean_inc(v___x_1182_);
v___x_1195_ = l_Lean_Name_replacePrefix(v___x_1182_, v___x_1187_, v___x_1194_);
lean_inc(v___x_1195_);
v___x_1196_ = l_Lean_Environment_contains(v_env_1193_, v___x_1195_, v_enabled_1181_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___x_1195_);
lean_dec(v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1182_);
v___x_1198_ = v___x_1177_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1182_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
uint8_t v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1177_);
v___x_1200_ = 0;
lean_inc(v___x_1195_);
v___x_1201_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v___x_1195_, v___x_1200_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref(v___x_1201_);
v___x_1202_ = lean_box(0);
v___x_1203_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_a_1175_, v___x_1195_, v___x_1202_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1211_);
v___x_1205_ = v___x_1203_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_dec(v___x_1203_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1182_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1182_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v___x_1182_);
v_a_1212_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1203_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1203_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v___x_1195_);
lean_dec(v___x_1182_);
lean_dec(v_a_1175_);
v_a_1220_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1201_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1201_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
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
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1174_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1174_);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_x_1237_, lean_object* v_stx_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_x_8450__boxed_1242_; lean_object* v_res_1243_; 
v_x_8450__boxed_1242_ = lean_unbox(v_x_1237_);
v_res_1243_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_x_8450__boxed_1242_, v_stx_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1277_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1278_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1276_, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_1281_, lean_object* v_m_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_1282_, v_a_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_1285_, v_m_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_m_1286_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11(lean_object* v_t_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___redArg(v_t_1289_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11___boxed(lean_object* v_t_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__11(v_t_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1300_, v_x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1303_, v_x_1304_, v_x_1305_);
lean_dec_ref(v_x_1305_);
lean_dec_ref(v_x_1304_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1308_, lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___redArg(v_a_1309_, v_x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1312_, lean_object* v_a_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_00_u03b2_1312_, v_a_1313_, v_x_1314_);
lean_dec(v_x_1314_);
lean_dec(v_a_1313_);
return v_res_1315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, size_t v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_1317_, v_x_1318_, v_x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
size_t v_x_8716__boxed_1325_; uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_x_8716__boxed_1325_ = lean_unbox_usize(v_x_1323_);
lean_dec(v_x_1323_);
v_res_1326_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1321_, v_x_1322_, v_x_8716__boxed_1325_, v_x_1324_);
lean_dec_ref(v_x_1324_);
lean_dec_ref(v_x_1322_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11(lean_object* v_00_u03b1_1328_, lean_object* v_constName_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___redArg(v_constName_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_constName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11(v_00_u03b1_1334_, v_constName_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1340_, lean_object* v_keys_1341_, lean_object* v_vals_1342_, lean_object* v_heq_1343_, lean_object* v_i_1344_, lean_object* v_k_1345_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1341_, v_i_1344_, v_k_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1347_, lean_object* v_keys_1348_, lean_object* v_vals_1349_, lean_object* v_heq_1350_, lean_object* v_i_1351_, lean_object* v_k_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1347_, v_keys_1348_, v_vals_1349_, v_heq_1350_, v_i_1351_, v_k_1352_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_vals_1349_);
lean_dec_ref(v_keys_1348_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15(lean_object* v_00_u03b1_1355_, lean_object* v_ref_1356_, lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg(v_ref_1356_, v_constName_1357_, v___y_1358_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_ref_1363_, lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15(v_00_u03b1_1362_, v_ref_1363_, v_constName_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_ref_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17(lean_object* v_00_u03b1_1369_, lean_object* v_ref_1370_, lean_object* v_msg_1371_, lean_object* v_declHint_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___redArg(v_ref_1370_, v_msg_1371_, v_declHint_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_ref_1378_, lean_object* v_msg_1379_, lean_object* v_declHint_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17(v_00_u03b1_1377_, v_ref_1378_, v_msg_1379_, v_declHint_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_1385_, lean_object* v_declHint_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_1385_, v_declHint_1386_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_1391_, lean_object* v_declHint_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__18_spec__19(v_msg_1391_, v_declHint_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_1397_, lean_object* v_ref_1398_, lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_1398_, v_msg_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_ref_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19(v_00_u03b1_1404_, v_ref_1405_, v_msg_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v_ref_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21(lean_object* v_00_u03b1_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___redArg(v_msg_1412_, v___y_1413_, v___y_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15_spec__17_spec__19_spec__21(v_00_u03b1_1417_, v_msg_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1426_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1427_ = l_Lean_addBuiltinDocString(v___x_1425_, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1457_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1458_ = l_Lean_addBuiltinDeclarationRanges(v___x_1456_, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1489_, uint8_t v___x_1490_, lean_object* v_id_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1489_, v___x_1490_);
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
v___x_1500_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1491_, v___x_1499_, v___y_1493_, v___y_1494_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1501_, lean_object* v___x_1502_, lean_object* v_id_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v___x_2590__boxed_1507_; lean_object* v_res_1508_; 
v___x_2590__boxed_1507_ = lean_unbox(v___x_1502_);
v_res_1508_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1501_, v___x_2590__boxed_1507_, v_id_1503_, v_x_1504_, v___y_1505_, v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_x_1504_);
lean_dec(v_id_1503_);
return v_res_1508_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1519_ = l_String_toRawSubstring_x27(v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___y_1527_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1523_);
v___x_1547_ = l_Lean_Syntax_isOfKind(v_x_1523_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_x_1523_);
v___x_1548_ = lean_box(1);
v___x_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_a_1525_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v_id_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v_id_1551_ = l_Lean_Syntax_getArg(v_x_1523_, v___x_1550_);
lean_dec(v_x_1523_);
v___x_1552_ = l_Lean_TSyntax_getId(v_id_1551_);
lean_inc(v___x_1552_);
v___x_1553_ = l_Lean_Macro_resolveGlobalName(v___x_1552_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
if (lean_obj_tag(v_a_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1553_);
v___x_1556_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1552_, v___x_1547_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__2));
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
v___x_1561_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1551_, v___x_1560_, v_a_1524_, v_a_1555_);
lean_dec(v_id_1551_);
v___y_1527_ = v___x_1561_;
goto v___jp_1526_;
}
else
{
lean_object* v_head_1562_; lean_object* v_snd_1563_; 
v_head_1562_ = lean_ctor_get(v_a_1554_, 0);
v_snd_1563_ = lean_ctor_get(v_head_1562_, 1);
if (lean_obj_tag(v_snd_1563_) == 0)
{
lean_object* v_tail_1564_; 
v_tail_1564_ = lean_ctor_get(v_a_1554_, 1);
if (lean_obj_tag(v_tail_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_head_1562_);
lean_dec_ref(v_a_1554_);
lean_dec(v___x_1552_);
v_a_1565_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1591_);
v___x_1567_ = v___x_1553_;
v_isShared_1568_ = v_isSharedCheck_1590_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1553_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1590_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; lean_object* v_quotContext_1570_; lean_object* v_currMacroScope_1571_; lean_object* v_ref_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_fst_1569_ = lean_ctor_get(v_head_1562_, 0);
lean_inc(v_fst_1569_);
lean_dec(v_head_1562_);
v_quotContext_1570_ = lean_ctor_get(v_a_1524_, 1);
v_currMacroScope_1571_ = lean_ctor_get(v_a_1524_, 2);
v_ref_1572_ = lean_ctor_get(v_a_1524_, 5);
v___x_1573_ = 0;
v___x_1574_ = l_Lean_SourceInfo_fromRef(v_ref_1572_, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1576_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1577_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1571_);
lean_inc(v_quotContext_1570_);
v___x_1578_ = l_Lean_addMacroScope(v_quotContext_1570_, v___x_1577_, v_currMacroScope_1571_);
v___x_1579_ = lean_box(0);
lean_inc_n(v___x_1574_, 2);
v___x_1580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1574_);
lean_ctor_set(v___x_1580_, 1, v___x_1576_);
lean_ctor_set(v___x_1580_, 2, v___x_1578_);
lean_ctor_set(v___x_1580_, 3, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_1582_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1583_ = l_Lean_Name_append(v___x_1582_, v_fst_1569_);
v___x_1584_ = l_Lean_mkIdentFrom(v_id_1551_, v___x_1583_, v___x_1547_);
lean_dec(v_id_1551_);
v___x_1585_ = l_Lean_Syntax_node1(v___x_1574_, v___x_1581_, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node2(v___x_1574_, v___x_1575_, v___x_1580_, v___x_1585_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1586_);
v___x_1588_ = v___x_1567_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1565_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1553_);
v___x_1593_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1552_, v___x_1547_, v_id_1551_, v_a_1554_, v_a_1524_, v_a_1592_);
lean_dec_ref(v_a_1554_);
lean_dec(v_id_1551_);
v___y_1527_ = v___x_1593_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1553_);
v___x_1595_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1552_, v___x_1547_, v_id_1551_, v_a_1554_, v_a_1524_, v_a_1594_);
lean_dec_ref(v_a_1554_);
lean_dec(v_id_1551_);
v___y_1527_ = v___x_1595_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v___x_1552_);
lean_dec(v_id_1551_);
v_a_1596_ = lean_ctor_get(v___x_1553_, 0);
v_a_1597_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1553_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_inc(v_a_1596_);
lean_dec(v___x_1553_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1596_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1526_:
{
if (lean_obj_tag(v___y_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1528_ = lean_ctor_get(v___y_1527_, 0);
v_a_1529_ = lean_ctor_get(v___y_1527_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___y_1527_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___y_1527_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_inc(v_a_1528_);
lean_dec(v___y_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1528_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1537_ = lean_ctor_get(v___y_1527_, 0);
v_a_1538_ = lean_ctor_get(v___y_1527_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___y_1527_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___y_1527_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_inc(v_a_1537_);
lean_dec(v___y_1527_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_a_1538_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1605_, v_a_1606_, v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1609_){
_start:
{
lean_object* v_subExpr_1611_; lean_object* v_expr_1612_; lean_object* v___x_1613_; 
v_subExpr_1611_ = lean_ctor_get(v___y_1609_, 3);
v_expr_1612_ = lean_ctor_get(v_subExpr_1611_, 0);
lean_inc_ref(v_expr_1612_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_expr_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1614_);
lean_dec_ref(v___y_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1617_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1633_, lean_object* v_us_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1636_ = l_Lean_Name_append(v___x_1635_, v_c_1633_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1637_, lean_object* v_us_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1637_, v_us_1638_);
lean_dec(v_us_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1645_);
lean_dec(v_x_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1757_; 
v___x_1681_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1674_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1757_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1757_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
switch(lean_obj_tag(v_a_1682_))
{
case 0:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_dec_ref(v_a_1682_);
v___x_1686_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
case 1:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
lean_dec_ref(v_a_1682_);
v___x_1690_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1690_);
v___x_1692_ = v___x_1684_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
case 2:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec_ref(v_a_1682_);
v___x_1694_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1694_);
v___x_1696_ = v___x_1684_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
case 3:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec_ref(v_a_1682_);
v___x_1698_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1698_);
v___x_1700_ = v___x_1684_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
case 4:
{
lean_object* v_declName_1702_; lean_object* v_us_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v_declName_1702_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v_declName_1702_);
v_us_1703_ = lean_ctor_get(v_a_1682_, 1);
lean_inc(v_us_1703_);
lean_dec_ref(v_a_1682_);
v___x_1704_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1702_, v_us_1703_);
lean_dec(v_us_1703_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1704_);
v___x_1706_ = v___x_1684_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
case 5:
{
lean_object* v_fn_1708_; lean_object* v___x_1709_; 
v_fn_1708_ = lean_ctor_get(v_a_1682_, 0);
lean_inc_ref(v_fn_1708_);
lean_dec_ref(v_a_1682_);
v___x_1709_ = l_Lean_Expr_getAppFn(v_fn_1708_);
lean_dec_ref(v_fn_1708_);
if (lean_obj_tag(v___x_1709_) == 4)
{
lean_object* v_declName_1710_; lean_object* v_us_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_declName_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_declName_1710_);
v_us_1711_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_us_1711_);
lean_dec_ref(v___x_1709_);
v___x_1712_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1710_, v_us_1711_);
lean_dec(v_us_1711_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1712_);
v___x_1714_ = v___x_1684_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec_ref(v___x_1709_);
v___x_1716_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1716_);
v___x_1718_ = v___x_1684_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
case 6:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec_ref(v_a_1682_);
v___x_1720_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1720_);
v___x_1722_ = v___x_1684_;
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
case 7:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec_ref(v_a_1682_);
v___x_1724_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1724_);
v___x_1726_ = v___x_1684_;
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
case 8:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec_ref(v_a_1682_);
v___x_1728_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1728_);
v___x_1730_ = v___x_1684_;
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
case 9:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec_ref(v_a_1682_);
v___x_1732_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1732_);
v___x_1734_ = v___x_1684_;
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
case 10:
{
lean_object* v_data_1736_; 
v_data_1736_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v_data_1736_);
lean_dec_ref(v_a_1682_);
if (lean_obj_tag(v_data_1736_) == 1)
{
lean_object* v_tail_1737_; 
v_tail_1737_ = lean_ctor_get(v_data_1736_, 1);
if (lean_obj_tag(v_tail_1737_) == 0)
{
lean_object* v_head_1738_; lean_object* v_fst_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v_head_1738_ = lean_ctor_get(v_data_1736_, 0);
lean_inc(v_head_1738_);
lean_dec_ref(v_data_1736_);
v_fst_1739_ = lean_ctor_get(v_head_1738_, 0);
lean_inc(v_fst_1739_);
lean_dec(v_head_1738_);
v___x_1740_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1741_ = l_Lean_Name_append(v___x_1740_, v_fst_1739_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1741_);
v___x_1743_ = v___x_1684_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1736_);
lean_dec_ref(v_data_1736_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1745_);
v___x_1747_ = v___x_1684_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1736_);
lean_dec(v_data_1736_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1749_);
v___x_1751_ = v___x_1684_;
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
}
default: 
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_dec_ref(v_a_1682_);
v___x_1753_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1753_);
v___x_1755_ = v___x_1684_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1766_, lean_object* v_k_1767_, lean_object* v_v_1768_){
_start:
{
lean_object* v_map_1769_; uint8_t v_hasTrace_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1783_; 
v_map_1769_ = lean_ctor_get(v_o_1766_, 0);
v_hasTrace_1770_ = lean_ctor_get_uint8(v_o_1766_, sizeof(void*)*1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_o_1766_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1772_ = v_o_1766_;
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_map_1769_);
lean_dec(v_o_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; 
lean_inc(v_k_1767_);
v___x_1774_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1767_, v_v_1768_, v_map_1769_);
if (v_hasTrace_1770_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1778_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_1776_ = l_Lean_Name_isPrefixOf(v___x_1775_, v_k_1767_);
lean_dec(v_k_1767_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1778_ = v___x_1772_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1774_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*1, v___x_1776_);
return v___x_1778_;
}
}
else
{
lean_object* v___x_1781_; 
lean_dec(v_k_1767_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*1, v_hasTrace_1770_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1784_){
_start:
{
lean_object* v_subExpr_1786_; lean_object* v_pos_1787_; lean_object* v___x_1788_; 
v_subExpr_1786_ = lean_ctor_get(v___y_1784_, 3);
v_pos_1787_ = lean_ctor_get(v_subExpr_1786_, 1);
lean_inc(v_pos_1787_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_pos_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1789_);
lean_dec_ref(v___y_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1792_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1808_, lean_object* v_k_1809_){
_start:
{
if (lean_obj_tag(v_t_1808_) == 0)
{
lean_object* v_k_1810_; lean_object* v_v_1811_; lean_object* v_l_1812_; lean_object* v_r_1813_; uint8_t v___x_1814_; 
v_k_1810_ = lean_ctor_get(v_t_1808_, 1);
v_v_1811_ = lean_ctor_get(v_t_1808_, 2);
v_l_1812_ = lean_ctor_get(v_t_1808_, 3);
v_r_1813_ = lean_ctor_get(v_t_1808_, 4);
v___x_1814_ = lean_nat_dec_lt(v_k_1809_, v_k_1810_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_eq(v_k_1809_, v_k_1810_);
if (v___x_1815_ == 0)
{
v_t_1808_ = v_r_1813_;
goto _start;
}
else
{
lean_object* v___x_1817_; 
lean_inc(v_v_1811_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_v_1811_);
return v___x_1817_;
}
}
else
{
v_t_1808_ = v_l_1812_;
goto _start;
}
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1820_, lean_object* v_k_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1820_, v_k_1821_);
lean_dec(v_k_1821_);
lean_dec(v_t_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1823_, lean_object* v_x_1824_){
_start:
{
if (lean_obj_tag(v_x_1824_) == 0)
{
lean_object* v_k_1826_; lean_object* v_v_1827_; lean_object* v_l_1828_; lean_object* v_r_1829_; lean_object* v___x_1830_; lean_object* v_a_1831_; lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_k_1826_ = lean_ctor_get(v_x_1824_, 1);
lean_inc(v_k_1826_);
v_v_1827_ = lean_ctor_get(v_x_1824_, 2);
lean_inc(v_v_1827_);
v_l_1828_ = lean_ctor_get(v_x_1824_, 3);
lean_inc(v_l_1828_);
v_r_1829_ = lean_ctor_get(v_x_1824_, 4);
lean_inc(v_r_1829_);
lean_dec_ref(v_x_1824_);
v___x_1830_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1823_, v_l_1828_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v_a_1832_ = lean_ctor_get(v_a_1831_, 0);
lean_inc(v_a_1832_);
lean_dec(v_a_1831_);
v___x_1833_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1832_, v_k_1826_, v_v_1827_);
v_init_1823_ = v___x_1833_;
v_x_1824_ = v_r_1829_;
goto _start;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_init_1823_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1837_, v_x_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_options_1848_; lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1871_; 
v_options_1848_ = lean_ctor_get(v_a_1845_, 2);
v___x_1849_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1841_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1871_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1871_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_optionsPerPos_1854_; lean_object* v___x_1855_; 
v_optionsPerPos_1854_ = lean_ctor_get(v_a_1841_, 0);
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1854_, v_a_1850_);
lean_dec(v_a_1850_);
if (lean_obj_tag(v___x_1855_) == 1)
{
lean_object* v_val_1856_; lean_object* v_map_1857_; lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1852_);
v_val_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1856_);
lean_dec_ref(v___x_1855_);
v_map_1857_ = lean_ctor_get(v_val_1856_, 0);
lean_inc(v_map_1857_);
lean_dec(v_val_1856_);
lean_inc_ref(v_options_1848_);
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_options_1848_, v_map_1857_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_a_1863_; lean_object* v___x_1865_; 
v_a_1863_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_a_1863_);
lean_dec(v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_a_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v___x_1869_; 
lean_dec(v___x_1855_);
lean_inc_ref(v_options_1848_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_options_1848_);
v___x_1869_ = v___x_1852_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_options_1848_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1880_, lean_object* v_t_1881_, lean_object* v_k_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1881_, v_k_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1884_, lean_object* v_t_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1884_, v_t_1885_, v_k_1886_);
lean_dec(v_k_1886_);
lean_dec(v_t_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1888_, v_x_1889_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1898_, v_x_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_apply_1(v_opt_1908_, v_a_1917_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_opt_1908_);
v_a_1926_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1916_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1916_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_1943_, lean_object* v_opt_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_opt_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_1953_, v_opt_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_1963_, lean_object* v_d_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1963_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; uint8_t v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = lean_unbox(v_a_1973_);
lean_dec(v_a_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref(v_d_1964_);
v___x_1975_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
lean_inc(v_a_1970_);
lean_inc_ref(v_a_1969_);
lean_inc(v_a_1968_);
lean_inc_ref(v_a_1967_);
lean_inc(v_a_1966_);
lean_inc_ref(v_a_1965_);
v___x_1976_ = lean_apply_7(v_d_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, lean_box(0));
return v___x_1976_;
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_d_1964_);
v_a_1977_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1972_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1972_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_1985_, lean_object* v_d_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_1985_, v_d_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_1995_, lean_object* v_d_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1995_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; uint8_t v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2007_ = lean_apply_7(v_d_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, lean_box(0));
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; 
lean_dec_ref(v_d_1996_);
v___x_2008_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2017_, lean_object* v_d_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2017_, v_d_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2027_, lean_object* v_v_2028_, lean_object* v_t_2029_){
_start:
{
if (lean_obj_tag(v_t_2029_) == 0)
{
lean_object* v_size_2030_; lean_object* v_k_2031_; lean_object* v_v_2032_; lean_object* v_l_2033_; lean_object* v_r_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2315_; 
v_size_2030_ = lean_ctor_get(v_t_2029_, 0);
v_k_2031_ = lean_ctor_get(v_t_2029_, 1);
v_v_2032_ = lean_ctor_get(v_t_2029_, 2);
v_l_2033_ = lean_ctor_get(v_t_2029_, 3);
v_r_2034_ = lean_ctor_get(v_t_2029_, 4);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_t_2029_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2036_ = v_t_2029_;
v_isShared_2037_ = v_isSharedCheck_2315_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_r_2034_);
lean_inc(v_l_2033_);
lean_inc(v_v_2032_);
lean_inc(v_k_2031_);
lean_inc(v_size_2030_);
lean_dec(v_t_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2315_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_nat_dec_lt(v_k_2027_, v_k_2031_);
if (v___x_2038_ == 0)
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_nat_dec_eq(v_k_2027_, v_k_2031_);
if (v___x_2039_ == 0)
{
lean_object* v_impl_2040_; lean_object* v___x_2041_; 
lean_dec(v_size_2030_);
v_impl_2040_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2027_, v_v_2028_, v_r_2034_);
v___x_2041_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2033_) == 0)
{
lean_object* v_size_2042_; lean_object* v_size_2043_; lean_object* v_k_2044_; lean_object* v_v_2045_; lean_object* v_l_2046_; lean_object* v_r_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_size_2042_ = lean_ctor_get(v_l_2033_, 0);
v_size_2043_ = lean_ctor_get(v_impl_2040_, 0);
lean_inc(v_size_2043_);
v_k_2044_ = lean_ctor_get(v_impl_2040_, 1);
lean_inc(v_k_2044_);
v_v_2045_ = lean_ctor_get(v_impl_2040_, 2);
lean_inc(v_v_2045_);
v_l_2046_ = lean_ctor_get(v_impl_2040_, 3);
lean_inc(v_l_2046_);
v_r_2047_ = lean_ctor_get(v_impl_2040_, 4);
lean_inc(v_r_2047_);
v___x_2048_ = lean_unsigned_to_nat(3u);
v___x_2049_ = lean_nat_mul(v___x_2048_, v_size_2042_);
v___x_2050_ = lean_nat_dec_lt(v___x_2049_, v_size_2043_);
lean_dec(v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec(v_r_2047_);
lean_dec(v_l_2046_);
lean_dec(v_v_2045_);
lean_dec(v_k_2044_);
v___x_2051_ = lean_nat_add(v___x_2041_, v_size_2042_);
v___x_2052_ = lean_nat_add(v___x_2051_, v_size_2043_);
lean_dec(v_size_2043_);
lean_dec(v___x_2051_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_impl_2040_);
lean_ctor_set(v___x_2036_, 0, v___x_2052_);
v___x_2054_ = v___x_2036_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_l_2033_);
lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_impl_2040_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
else
{
lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2119_; 
v_isSharedCheck_2119_ = !lean_is_exclusive(v_impl_2040_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; 
v_unused_2120_ = lean_ctor_get(v_impl_2040_, 4);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_impl_2040_, 3);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_impl_2040_, 2);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_impl_2040_, 1);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_impl_2040_, 0);
lean_dec(v_unused_2124_);
v___x_2057_ = v_impl_2040_;
v_isShared_2058_ = v_isSharedCheck_2119_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v_impl_2040_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2119_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_size_2059_; lean_object* v_k_2060_; lean_object* v_v_2061_; lean_object* v_l_2062_; lean_object* v_r_2063_; lean_object* v_size_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_size_2059_ = lean_ctor_get(v_l_2046_, 0);
v_k_2060_ = lean_ctor_get(v_l_2046_, 1);
v_v_2061_ = lean_ctor_get(v_l_2046_, 2);
v_l_2062_ = lean_ctor_get(v_l_2046_, 3);
v_r_2063_ = lean_ctor_get(v_l_2046_, 4);
v_size_2064_ = lean_ctor_get(v_r_2047_, 0);
v___x_2065_ = lean_unsigned_to_nat(2u);
v___x_2066_ = lean_nat_mul(v___x_2065_, v_size_2064_);
v___x_2067_ = lean_nat_dec_lt(v_size_2059_, v___x_2066_);
lean_dec(v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2095_; 
lean_inc(v_r_2063_);
lean_inc(v_l_2062_);
lean_inc(v_v_2061_);
lean_inc(v_k_2060_);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_l_2046_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; lean_object* v_unused_2100_; 
v_unused_2096_ = lean_ctor_get(v_l_2046_, 4);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_l_2046_, 3);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_l_2046_, 2);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_l_2046_, 1);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_l_2046_, 0);
lean_dec(v_unused_2100_);
v___x_2069_ = v_l_2046_;
v_isShared_2070_ = v_isSharedCheck_2095_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v_l_2046_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2095_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2085_; 
v___x_2071_ = lean_nat_add(v___x_2041_, v_size_2042_);
v___x_2072_ = lean_nat_add(v___x_2071_, v_size_2043_);
lean_dec(v_size_2043_);
if (lean_obj_tag(v_l_2062_) == 0)
{
lean_object* v_size_2093_; 
v_size_2093_ = lean_ctor_get(v_l_2062_, 0);
lean_inc(v_size_2093_);
v___y_2085_ = v_size_2093_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_unsigned_to_nat(0u);
v___y_2085_ = v___x_2094_;
goto v___jp_2084_;
}
v___jp_2073_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_nat_add(v___y_2074_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec(v___y_2074_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_r_2047_);
lean_ctor_set(v___x_2069_, 3, v_r_2063_);
lean_ctor_set(v___x_2069_, 2, v_v_2045_);
lean_ctor_set(v___x_2069_, 1, v_k_2044_);
lean_ctor_set(v___x_2069_, 0, v___x_2077_);
v___x_2079_ = v___x_2069_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_k_2044_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_v_2045_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_r_2063_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_r_2047_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v___x_2079_);
lean_ctor_set(v___x_2057_, 3, v___y_2075_);
lean_ctor_set(v___x_2057_, 2, v_v_2061_);
lean_ctor_set(v___x_2057_, 1, v_k_2060_);
lean_ctor_set(v___x_2057_, 0, v___x_2072_);
v___x_2081_ = v___x_2057_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_2060_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v___y_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_nat_add(v___x_2071_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec(v___x_2071_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_l_2062_);
lean_ctor_set(v___x_2036_, 0, v___x_2086_);
v___x_2088_ = v___x_2036_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_2033_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_l_2062_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_nat_add(v___x_2041_, v_size_2064_);
if (lean_obj_tag(v_r_2063_) == 0)
{
lean_object* v_size_2090_; 
v_size_2090_ = lean_ctor_get(v_r_2063_, 0);
lean_inc(v_size_2090_);
v___y_2074_ = v___x_2089_;
v___y_2075_ = v___x_2088_;
v___y_2076_ = v_size_2090_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___y_2074_ = v___x_2089_;
v___y_2075_ = v___x_2088_;
v___y_2076_ = v___x_2091_;
goto v___jp_2073_;
}
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_del_object(v___x_2036_);
v___x_2101_ = lean_nat_add(v___x_2041_, v_size_2042_);
v___x_2102_ = lean_nat_add(v___x_2101_, v_size_2043_);
lean_dec(v_size_2043_);
v___x_2103_ = lean_nat_add(v___x_2101_, v_size_2059_);
lean_dec(v___x_2101_);
lean_inc_ref(v_l_2033_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v_l_2046_);
lean_ctor_set(v___x_2057_, 3, v_l_2033_);
lean_ctor_set(v___x_2057_, 2, v_v_2032_);
lean_ctor_set(v___x_2057_, 1, v_k_2031_);
lean_ctor_set(v___x_2057_, 0, v___x_2103_);
v___x_2105_ = v___x_2057_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_l_2033_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_l_2046_);
v___x_2105_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_isSharedCheck_2112_ = !lean_is_exclusive(v_l_2033_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2113_ = lean_ctor_get(v_l_2033_, 4);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_l_2033_, 3);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_l_2033_, 2);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_l_2033_, 1);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_l_2033_, 0);
lean_dec(v_unused_2117_);
v___x_2107_ = v_l_2033_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v_l_2033_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 4, v_r_2047_);
lean_ctor_set(v___x_2107_, 3, v___x_2105_);
lean_ctor_set(v___x_2107_, 2, v_v_2045_);
lean_ctor_set(v___x_2107_, 1, v_k_2044_);
lean_ctor_set(v___x_2107_, 0, v___x_2102_);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_2044_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_2045_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_r_2047_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2125_; 
v_l_2125_ = lean_ctor_get(v_impl_2040_, 3);
lean_inc(v_l_2125_);
if (lean_obj_tag(v_l_2125_) == 0)
{
lean_object* v_r_2126_; lean_object* v_k_2127_; lean_object* v_v_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2151_; 
v_r_2126_ = lean_ctor_get(v_impl_2040_, 4);
v_k_2127_ = lean_ctor_get(v_impl_2040_, 1);
v_v_2128_ = lean_ctor_get(v_impl_2040_, 2);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_impl_2040_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2152_ = lean_ctor_get(v_impl_2040_, 3);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_impl_2040_, 0);
lean_dec(v_unused_2153_);
v___x_2130_ = v_impl_2040_;
v_isShared_2131_ = v_isSharedCheck_2151_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_r_2126_);
lean_inc(v_v_2128_);
lean_inc(v_k_2127_);
lean_dec(v_impl_2040_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2151_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_k_2132_; lean_object* v_v_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_k_2132_ = lean_ctor_get(v_l_2125_, 1);
v_v_2133_ = lean_ctor_get(v_l_2125_, 2);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_l_2125_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; 
v_unused_2148_ = lean_ctor_get(v_l_2125_, 4);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2125_, 3);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2125_, 0);
lean_dec(v_unused_2150_);
v___x_2135_ = v_l_2125_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_v_2133_);
lean_inc(v_k_2132_);
lean_dec(v_l_2125_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2126_, 2);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 4, v_r_2126_);
lean_ctor_set(v___x_2135_, 3, v_r_2126_);
lean_ctor_set(v___x_2135_, 2, v_v_2032_);
lean_ctor_set(v___x_2135_, 1, v_k_2031_);
lean_ctor_set(v___x_2135_, 0, v___x_2041_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_r_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_r_2126_);
v___x_2139_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
lean_inc(v_r_2126_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 3, v_r_2126_);
lean_ctor_set(v___x_2130_, 0, v___x_2041_);
v___x_2141_ = v___x_2130_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2127_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2128_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_r_2126_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_2126_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v___x_2141_);
lean_ctor_set(v___x_2036_, 3, v___x_2139_);
lean_ctor_set(v___x_2036_, 2, v_v_2133_);
lean_ctor_set(v___x_2036_, 1, v_k_2132_);
lean_ctor_set(v___x_2036_, 0, v___x_2137_);
v___x_2143_ = v___x_2036_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2132_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2133_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
else
{
lean_object* v_r_2154_; 
v_r_2154_ = lean_ctor_get(v_impl_2040_, 4);
lean_inc(v_r_2154_);
if (lean_obj_tag(v_r_2154_) == 0)
{
lean_object* v_k_2155_; lean_object* v_v_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2167_; 
v_k_2155_ = lean_ctor_get(v_impl_2040_, 1);
v_v_2156_ = lean_ctor_get(v_impl_2040_, 2);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_impl_2040_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2168_ = lean_ctor_get(v_impl_2040_, 4);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_impl_2040_, 3);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_impl_2040_, 0);
lean_dec(v_unused_2170_);
v___x_2158_ = v_impl_2040_;
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_v_2156_);
lean_inc(v_k_2155_);
lean_dec(v_impl_2040_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_unsigned_to_nat(3u);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 4, v_l_2125_);
lean_ctor_set(v___x_2158_, 2, v_v_2032_);
lean_ctor_set(v___x_2158_, 1, v_k_2031_);
lean_ctor_set(v___x_2158_, 0, v___x_2041_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_l_2125_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_l_2125_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_r_2154_);
lean_ctor_set(v___x_2036_, 3, v___x_2162_);
lean_ctor_set(v___x_2036_, 2, v_v_2156_);
lean_ctor_set(v___x_2036_, 1, v_k_2155_);
lean_ctor_set(v___x_2036_, 0, v___x_2160_);
v___x_2164_ = v___x_2036_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_2155_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_2156_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_r_2154_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_unsigned_to_nat(2u);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_impl_2040_);
lean_ctor_set(v___x_2036_, 3, v_r_2154_);
lean_ctor_set(v___x_2036_, 0, v___x_2171_);
v___x_2173_ = v___x_2036_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_r_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_impl_2040_);
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
else
{
lean_object* v___x_2176_; 
lean_dec(v_v_2032_);
lean_dec(v_k_2031_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 2, v_v_2028_);
lean_ctor_set(v___x_2036_, 1, v_k_2027_);
v___x_2176_ = v___x_2036_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_size_2030_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2027_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2028_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_l_2033_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_r_2034_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
else
{
lean_object* v_impl_2178_; lean_object* v___x_2179_; 
lean_dec(v_size_2030_);
v_impl_2178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2027_, v_v_2028_, v_l_2033_);
v___x_2179_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2034_) == 0)
{
lean_object* v_size_2180_; lean_object* v_size_2181_; lean_object* v_k_2182_; lean_object* v_v_2183_; lean_object* v_l_2184_; lean_object* v_r_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_size_2180_ = lean_ctor_get(v_r_2034_, 0);
v_size_2181_ = lean_ctor_get(v_impl_2178_, 0);
lean_inc(v_size_2181_);
v_k_2182_ = lean_ctor_get(v_impl_2178_, 1);
lean_inc(v_k_2182_);
v_v_2183_ = lean_ctor_get(v_impl_2178_, 2);
lean_inc(v_v_2183_);
v_l_2184_ = lean_ctor_get(v_impl_2178_, 3);
lean_inc(v_l_2184_);
v_r_2185_ = lean_ctor_get(v_impl_2178_, 4);
lean_inc(v_r_2185_);
v___x_2186_ = lean_unsigned_to_nat(3u);
v___x_2187_ = lean_nat_mul(v___x_2186_, v_size_2180_);
v___x_2188_ = lean_nat_dec_lt(v___x_2187_, v_size_2181_);
lean_dec(v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec(v_r_2185_);
lean_dec(v_l_2184_);
lean_dec(v_v_2183_);
lean_dec(v_k_2182_);
v___x_2189_ = lean_nat_add(v___x_2179_, v_size_2181_);
lean_dec(v_size_2181_);
v___x_2190_ = lean_nat_add(v___x_2189_, v_size_2180_);
lean_dec(v___x_2189_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 3, v_impl_2178_);
lean_ctor_set(v___x_2036_, 0, v___x_2190_);
v___x_2192_ = v___x_2036_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2193_, 4, v_r_2034_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2259_; 
v_isSharedCheck_2259_ = !lean_is_exclusive(v_impl_2178_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; 
v_unused_2260_ = lean_ctor_get(v_impl_2178_, 4);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2178_, 3);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_impl_2178_, 2);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_impl_2178_, 1);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_impl_2178_, 0);
lean_dec(v_unused_2264_);
v___x_2195_ = v_impl_2178_;
v_isShared_2196_ = v_isSharedCheck_2259_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v_impl_2178_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2259_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_size_2197_; lean_object* v_size_2198_; lean_object* v_k_2199_; lean_object* v_v_2200_; lean_object* v_l_2201_; lean_object* v_r_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_size_2197_ = lean_ctor_get(v_l_2184_, 0);
v_size_2198_ = lean_ctor_get(v_r_2185_, 0);
v_k_2199_ = lean_ctor_get(v_r_2185_, 1);
v_v_2200_ = lean_ctor_get(v_r_2185_, 2);
v_l_2201_ = lean_ctor_get(v_r_2185_, 3);
v_r_2202_ = lean_ctor_get(v_r_2185_, 4);
v___x_2203_ = lean_unsigned_to_nat(2u);
v___x_2204_ = lean_nat_mul(v___x_2203_, v_size_2197_);
v___x_2205_ = lean_nat_dec_lt(v_size_2198_, v___x_2204_);
lean_dec(v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2234_; 
lean_inc(v_r_2202_);
lean_inc(v_l_2201_);
lean_inc(v_v_2200_);
lean_inc(v_k_2199_);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_r_2185_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; lean_object* v_unused_2236_; lean_object* v_unused_2237_; lean_object* v_unused_2238_; lean_object* v_unused_2239_; 
v_unused_2235_ = lean_ctor_get(v_r_2185_, 4);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_r_2185_, 3);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_r_2185_, 2);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_r_2185_, 1);
lean_dec(v_unused_2238_);
v_unused_2239_ = lean_ctor_get(v_r_2185_, 0);
lean_dec(v_unused_2239_);
v___x_2207_ = v_r_2185_;
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v_r_2185_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___x_2222_; lean_object* v___y_2224_; 
v___x_2209_ = lean_nat_add(v___x_2179_, v_size_2181_);
lean_dec(v_size_2181_);
v___x_2210_ = lean_nat_add(v___x_2209_, v_size_2180_);
lean_dec(v___x_2209_);
v___x_2222_ = lean_nat_add(v___x_2179_, v_size_2197_);
if (lean_obj_tag(v_l_2201_) == 0)
{
lean_object* v_size_2232_; 
v_size_2232_ = lean_ctor_get(v_l_2201_, 0);
lean_inc(v_size_2232_);
v___y_2224_ = v_size_2232_;
goto v___jp_2223_;
}
else
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_unsigned_to_nat(0u);
v___y_2224_ = v___x_2233_;
goto v___jp_2223_;
}
v___jp_2211_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_nat_add(v___y_2212_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec(v___y_2212_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 4, v_r_2034_);
lean_ctor_set(v___x_2207_, 3, v_r_2202_);
lean_ctor_set(v___x_2207_, 2, v_v_2032_);
lean_ctor_set(v___x_2207_, 1, v_k_2031_);
lean_ctor_set(v___x_2207_, 0, v___x_2215_);
v___x_2217_ = v___x_2207_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_r_2202_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_r_2034_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v___x_2217_);
lean_ctor_set(v___x_2195_, 3, v___y_2213_);
lean_ctor_set(v___x_2195_, 2, v_v_2200_);
lean_ctor_set(v___x_2195_, 1, v_k_2199_);
lean_ctor_set(v___x_2195_, 0, v___x_2210_);
v___x_2219_ = v___x_2195_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_k_2199_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_v_2200_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v___y_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_nat_add(v___x_2222_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec(v___x_2222_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_l_2201_);
lean_ctor_set(v___x_2036_, 3, v_l_2184_);
lean_ctor_set(v___x_2036_, 2, v_v_2183_);
lean_ctor_set(v___x_2036_, 1, v_k_2182_);
lean_ctor_set(v___x_2036_, 0, v___x_2225_);
v___x_2227_ = v___x_2036_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_l_2184_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_l_2201_);
v___x_2227_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_nat_add(v___x_2179_, v_size_2180_);
if (lean_obj_tag(v_r_2202_) == 0)
{
lean_object* v_size_2229_; 
v_size_2229_ = lean_ctor_get(v_r_2202_, 0);
lean_inc(v_size_2229_);
v___y_2212_ = v___x_2228_;
v___y_2213_ = v___x_2227_;
v___y_2214_ = v_size_2229_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_unsigned_to_nat(0u);
v___y_2212_ = v___x_2228_;
v___y_2213_ = v___x_2227_;
v___y_2214_ = v___x_2230_;
goto v___jp_2211_;
}
}
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_del_object(v___x_2036_);
v___x_2240_ = lean_nat_add(v___x_2179_, v_size_2181_);
lean_dec(v_size_2181_);
v___x_2241_ = lean_nat_add(v___x_2240_, v_size_2180_);
lean_dec(v___x_2240_);
v___x_2242_ = lean_nat_add(v___x_2179_, v_size_2180_);
v___x_2243_ = lean_nat_add(v___x_2242_, v_size_2198_);
lean_dec(v___x_2242_);
lean_inc_ref(v_r_2034_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v_r_2034_);
lean_ctor_set(v___x_2195_, 3, v_r_2185_);
lean_ctor_set(v___x_2195_, 2, v_v_2032_);
lean_ctor_set(v___x_2195_, 1, v_k_2031_);
lean_ctor_set(v___x_2195_, 0, v___x_2243_);
v___x_2245_ = v___x_2195_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_r_2185_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_r_2034_);
v___x_2245_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_isSharedCheck_2252_ = !lean_is_exclusive(v_r_2034_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2253_ = lean_ctor_get(v_r_2034_, 4);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_r_2034_, 3);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_r_2034_, 2);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_r_2034_, 1);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_r_2034_, 0);
lean_dec(v_unused_2257_);
v___x_2247_ = v_r_2034_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v_r_2034_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 4, v___x_2245_);
lean_ctor_set(v___x_2247_, 3, v_l_2184_);
lean_ctor_set(v___x_2247_, 2, v_v_2183_);
lean_ctor_set(v___x_2247_, 1, v_k_2182_);
lean_ctor_set(v___x_2247_, 0, v___x_2241_);
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_l_2184_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v___x_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2265_; 
v_l_2265_ = lean_ctor_get(v_impl_2178_, 3);
lean_inc(v_l_2265_);
if (lean_obj_tag(v_l_2265_) == 0)
{
lean_object* v_r_2266_; lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2279_; 
v_r_2266_ = lean_ctor_get(v_impl_2178_, 4);
v_k_2267_ = lean_ctor_get(v_impl_2178_, 1);
v_v_2268_ = lean_ctor_get(v_impl_2178_, 2);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_impl_2178_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; lean_object* v_unused_2281_; 
v_unused_2280_ = lean_ctor_get(v_impl_2178_, 3);
lean_dec(v_unused_2280_);
v_unused_2281_ = lean_ctor_get(v_impl_2178_, 0);
lean_dec(v_unused_2281_);
v___x_2270_ = v_impl_2178_;
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_r_2266_);
lean_inc(v_v_2268_);
lean_inc(v_k_2267_);
lean_dec(v_impl_2178_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2266_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 3, v_r_2266_);
lean_ctor_set(v___x_2270_, 2, v_v_2032_);
lean_ctor_set(v___x_2270_, 1, v_k_2031_);
lean_ctor_set(v___x_2270_, 0, v___x_2179_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_r_2266_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v_r_2266_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v___x_2274_);
lean_ctor_set(v___x_2036_, 3, v_l_2265_);
lean_ctor_set(v___x_2036_, 2, v_v_2268_);
lean_ctor_set(v___x_2036_, 1, v_k_2267_);
lean_ctor_set(v___x_2036_, 0, v___x_2272_);
v___x_2276_ = v___x_2036_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_k_2267_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_v_2268_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_l_2265_);
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
}
else
{
lean_object* v_r_2282_; 
v_r_2282_ = lean_ctor_get(v_impl_2178_, 4);
lean_inc(v_r_2282_);
if (lean_obj_tag(v_r_2282_) == 0)
{
lean_object* v_k_2283_; lean_object* v_v_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2307_; 
v_k_2283_ = lean_ctor_get(v_impl_2178_, 1);
v_v_2284_ = lean_ctor_get(v_impl_2178_, 2);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_impl_2178_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; 
v_unused_2308_ = lean_ctor_get(v_impl_2178_, 4);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_impl_2178_, 3);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_impl_2178_, 0);
lean_dec(v_unused_2310_);
v___x_2286_ = v_impl_2178_;
v_isShared_2287_ = v_isSharedCheck_2307_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_v_2284_);
lean_inc(v_k_2283_);
lean_dec(v_impl_2178_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2307_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_k_2288_; lean_object* v_v_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2303_; 
v_k_2288_ = lean_ctor_get(v_r_2282_, 1);
v_v_2289_ = lean_ctor_get(v_r_2282_, 2);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_r_2282_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; 
v_unused_2304_ = lean_ctor_get(v_r_2282_, 4);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_r_2282_, 3);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_r_2282_, 0);
lean_dec(v_unused_2306_);
v___x_2291_ = v_r_2282_;
v_isShared_2292_ = v_isSharedCheck_2303_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_v_2289_);
lean_inc(v_k_2288_);
lean_dec(v_r_2282_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2303_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = lean_unsigned_to_nat(3u);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_l_2265_);
lean_ctor_set(v___x_2291_, 3, v_l_2265_);
lean_ctor_set(v___x_2291_, 2, v_v_2284_);
lean_ctor_set(v___x_2291_, 1, v_k_2283_);
lean_ctor_set(v___x_2291_, 0, v___x_2179_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_l_2265_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_l_2265_);
v___x_2295_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2297_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 4, v_l_2265_);
lean_ctor_set(v___x_2286_, 2, v_v_2032_);
lean_ctor_set(v___x_2286_, 1, v_k_2031_);
lean_ctor_set(v___x_2286_, 0, v___x_2179_);
v___x_2297_ = v___x_2286_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v_l_2265_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v_l_2265_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v___x_2297_);
lean_ctor_set(v___x_2036_, 3, v___x_2295_);
lean_ctor_set(v___x_2036_, 2, v_v_2289_);
lean_ctor_set(v___x_2036_, 1, v_k_2288_);
lean_ctor_set(v___x_2036_, 0, v___x_2293_);
v___x_2299_ = v___x_2036_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2289_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_unsigned_to_nat(2u);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v_r_2282_);
lean_ctor_set(v___x_2036_, 3, v_impl_2178_);
lean_ctor_set(v___x_2036_, 0, v___x_2311_);
v___x_2313_ = v___x_2036_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_k_2031_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_v_2032_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_r_2282_);
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
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_unsigned_to_nat(1u);
v___x_2317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_k_2027_);
lean_ctor_set(v___x_2317_, 2, v_v_2028_);
lean_ctor_set(v___x_2317_, 3, v_t_2029_);
lean_ctor_set(v___x_2317_, 4, v_t_2029_);
return v___x_2317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2318_, lean_object* v_v_2319_, lean_object* v_x_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v_optionsPerPos_2330_; lean_object* v_currNamespace_2331_; lean_object* v_openDecls_2332_; uint8_t v_inPattern_2333_; lean_object* v_subExpr_2334_; lean_object* v_depth_2335_; lean_object* v___y_2337_; lean_object* v___x_2342_; 
v___x_2328_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2321_);
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v_optionsPerPos_2330_ = lean_ctor_get(v_a_2321_, 0);
v_currNamespace_2331_ = lean_ctor_get(v_a_2321_, 1);
v_openDecls_2332_ = lean_ctor_get(v_a_2321_, 2);
v_inPattern_2333_ = lean_ctor_get_uint8(v_a_2321_, sizeof(void*)*5);
v_subExpr_2334_ = lean_ctor_get(v_a_2321_, 3);
v_depth_2335_ = lean_ctor_get(v_a_2321_, 4);
v___x_2342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2330_, v_a_2329_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Options_empty;
v___y_2337_ = v___x_2343_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_val_2344_);
lean_dec_ref(v___x_2342_);
v___y_2337_ = v_val_2344_;
goto v___jp_2336_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2337_, v_k_2318_, v_v_2319_);
lean_inc(v_optionsPerPos_2330_);
v___x_2339_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2329_, v___x_2338_, v_optionsPerPos_2330_);
lean_inc(v_depth_2335_);
lean_inc_ref(v_subExpr_2334_);
lean_inc(v_openDecls_2332_);
lean_inc(v_currNamespace_2331_);
v___x_2340_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v_currNamespace_2331_);
lean_ctor_set(v___x_2340_, 2, v_openDecls_2332_);
lean_ctor_set(v___x_2340_, 3, v_subExpr_2334_);
lean_ctor_set(v___x_2340_, 4, v_depth_2335_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*5, v_inPattern_2333_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_a_2323_);
lean_inc(v_a_2322_);
v___x_2341_ = lean_apply_7(v_x_2320_, v___x_2340_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, lean_box(0));
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2345_, lean_object* v_v_2346_, lean_object* v_x_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2345_, v_v_2346_, v_x_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2356_, lean_object* v_k_2357_, lean_object* v_v_2358_, lean_object* v_x_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2357_, v_v_2358_, v_x_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_k_2369_, lean_object* v_v_2370_, lean_object* v_x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2368_, v_k_2369_, v_v_2370_, v_x_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2380_, lean_object* v_k_2381_, lean_object* v_v_2382_, lean_object* v_t_2383_, lean_object* v_hl_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2381_, v_v_2382_, v_t_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2386_, lean_object* v_stx_2387_){
_start:
{
uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = 0;
lean_inc(v_pos_2386_);
v___x_2389_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2389_, 0, v_pos_2386_);
lean_ctor_set(v___x_2389_, 1, v_pos_2386_);
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*2, v___x_2388_);
v___x_2390_ = l_Lean_Syntax_setInfo(v___x_2389_, v_stx_2387_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
v___x_2394_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2392_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2395_, v_stx_2391_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2404_, v_a_2405_);
lean_dec_ref(v_a_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2408_, v_a_2409_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2428_, lean_object* v_e_2429_, uint8_t v_isBinder_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_lctx_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_lctx_2433_ = lean_ctor_get(v_a_2431_, 2);
v___x_2434_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v_stx_2428_);
v___x_2436_ = lean_box(0);
v___x_2437_ = 0;
lean_inc_ref(v_lctx_2433_);
v___x_2438_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2438_, 0, v___x_2435_);
lean_ctor_set(v___x_2438_, 1, v_lctx_2433_);
lean_ctor_set(v___x_2438_, 2, v___x_2436_);
lean_ctor_set(v___x_2438_, 3, v_e_2429_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*4, v_isBinder_2430_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*4 + 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2440_, lean_object* v_e_2441_, lean_object* v_isBinder_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
uint8_t v_isBinder_boxed_2445_; lean_object* v_res_2446_; 
v_isBinder_boxed_2445_ = lean_unbox(v_isBinder_2442_);
v_res_2446_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2440_, v_e_2441_, v_isBinder_boxed_2445_, v_a_2443_);
lean_dec_ref(v_a_2443_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2447_, lean_object* v_e_2448_, uint8_t v_isBinder_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2447_, v_e_2448_, v_isBinder_2449_, v_a_2452_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2458_, lean_object* v_e_2459_, lean_object* v_isBinder_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
uint8_t v_isBinder_boxed_2468_; lean_object* v_res_2469_; 
v_isBinder_boxed_2468_ = lean_unbox(v_isBinder_2460_);
v_res_2469_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2458_, v_e_2459_, v_isBinder_boxed_2468_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2470_, lean_object* v_stx_2471_, lean_object* v_e_2472_, uint8_t v_isBinder_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2500_; 
v___x_2477_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2471_, v_e_2472_, v_isBinder_2473_, v_a_2475_);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2500_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2500_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v_steps_2483_; lean_object* v_infos_2484_; lean_object* v_holeIter_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2499_; 
v___x_2482_ = lean_st_ref_take(v_a_2474_);
v_steps_2483_ = lean_ctor_get(v___x_2482_, 0);
v_infos_2484_ = lean_ctor_get(v___x_2482_, 1);
v_holeIter_2485_ = lean_ctor_get(v___x_2482_, 2);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2487_ = v___x_2482_;
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_holeIter_2485_);
lean_inc(v_infos_2484_);
lean_inc(v_steps_2483_);
lean_dec(v___x_2482_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2478_);
v___x_2490_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2470_, v___x_2489_, v_infos_2484_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_steps_2483_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_holeIter_2485_);
v___x_2492_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2493_ = lean_st_ref_set(v_a_2474_, v___x_2492_);
v___x_2494_ = lean_box(0);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2494_);
v___x_2496_ = v___x_2480_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2501_, lean_object* v_stx_2502_, lean_object* v_e_2503_, lean_object* v_isBinder_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
uint8_t v_isBinder_boxed_2508_; lean_object* v_res_2509_; 
v_isBinder_boxed_2508_ = lean_unbox(v_isBinder_2504_);
v_res_2509_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2501_, v_stx_2502_, v_e_2503_, v_isBinder_boxed_2508_, v_a_2505_, v_a_2506_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2510_, lean_object* v_stx_2511_, lean_object* v_e_2512_, uint8_t v_isBinder_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2510_, v_stx_2511_, v_e_2512_, v_isBinder_2513_, v_a_2515_, v_a_2516_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2522_, lean_object* v_stx_2523_, lean_object* v_e_2524_, lean_object* v_isBinder_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
uint8_t v_isBinder_boxed_2533_; lean_object* v_res_2534_; 
v_isBinder_boxed_2533_ = lean_unbox(v_isBinder_2525_);
v_res_2534_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2522_, v_stx_2523_, v_e_2524_, v_isBinder_boxed_2533_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2535_, lean_object* v_fieldName_2536_, lean_object* v_stx_2537_, lean_object* v_val_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_lctx_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_lctx_2541_ = lean_ctor_get(v_a_2539_, 2);
lean_inc_ref(v_lctx_2541_);
v___x_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2542_, 0, v_projName_2535_);
lean_ctor_set(v___x_2542_, 1, v_fieldName_2536_);
lean_ctor_set(v___x_2542_, 2, v_lctx_2541_);
lean_ctor_set(v___x_2542_, 3, v_val_2538_);
lean_ctor_set(v___x_2542_, 4, v_stx_2537_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2544_, lean_object* v_fieldName_2545_, lean_object* v_stx_2546_, lean_object* v_val_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2544_, v_fieldName_2545_, v_stx_2546_, v_val_2547_, v_a_2548_);
lean_dec_ref(v_a_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2551_, lean_object* v_fieldName_2552_, lean_object* v_stx_2553_, lean_object* v_val_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2551_, v_fieldName_2552_, v_stx_2553_, v_val_2554_, v_a_2557_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2563_, lean_object* v_fieldName_2564_, lean_object* v_stx_2565_, lean_object* v_val_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2563_, v_fieldName_2564_, v_stx_2565_, v_val_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2575_, lean_object* v_projName_2576_, lean_object* v_fieldName_2577_, lean_object* v_stx_2578_, lean_object* v_val_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2606_; 
v___x_2583_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2576_, v_fieldName_2577_, v_stx_2578_, v_val_2579_, v_a_2581_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2606_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2606_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v_steps_2589_; lean_object* v_infos_2590_; lean_object* v_holeIter_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2605_; 
v___x_2588_ = lean_st_ref_take(v_a_2580_);
v_steps_2589_ = lean_ctor_get(v___x_2588_, 0);
v_infos_2590_ = lean_ctor_get(v___x_2588_, 1);
v_holeIter_2591_ = lean_ctor_get(v___x_2588_, 2);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2593_ = v___x_2588_;
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_holeIter_2591_);
lean_inc(v_infos_2590_);
lean_inc(v_steps_2589_);
lean_dec(v___x_2588_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_a_2584_);
v___x_2596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2575_, v___x_2595_, v_infos_2590_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_steps_2589_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_holeIter_2591_);
v___x_2598_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = lean_st_ref_set(v_a_2580_, v___x_2598_);
v___x_2600_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2600_);
v___x_2602_ = v___x_2586_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2607_, lean_object* v_projName_2608_, lean_object* v_fieldName_2609_, lean_object* v_stx_2610_, lean_object* v_val_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2607_, v_projName_2608_, v_fieldName_2609_, v_stx_2610_, v_val_2611_, v_a_2612_, v_a_2613_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2616_, lean_object* v_projName_2617_, lean_object* v_fieldName_2618_, lean_object* v_stx_2619_, lean_object* v_val_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2616_, v_projName_2617_, v_fieldName_2618_, v_stx_2619_, v_val_2620_, v_a_2622_, v_a_2623_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2629_, lean_object* v_projName_2630_, lean_object* v_fieldName_2631_, lean_object* v_stx_2632_, lean_object* v_val_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2629_, v_projName_2630_, v_fieldName_2631_, v_stx_2632_, v_val_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2642_, lean_object* v_stx_2643_, lean_object* v_e_2644_, uint8_t v_isBinder_2645_, lean_object* v_location_x3f_2646_, lean_object* v_docString_x3f_2647_, uint8_t v_explicit_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2676_; 
v___x_2652_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2643_, v_e_2644_, v_isBinder_2645_, v_a_2650_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2676_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2676_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v_steps_2658_; lean_object* v_infos_2659_; lean_object* v_holeIter_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2675_; 
v___x_2657_ = lean_st_ref_take(v_a_2649_);
v_steps_2658_ = lean_ctor_get(v___x_2657_, 0);
v_infos_2659_ = lean_ctor_get(v___x_2657_, 1);
v_holeIter_2660_ = lean_ctor_get(v___x_2657_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2662_ = v___x_2657_;
v_isShared_2663_ = v_isSharedCheck_2675_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_holeIter_2660_);
lean_inc(v_infos_2659_);
lean_inc(v_steps_2658_);
lean_dec(v___x_2657_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2675_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2664_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2664_, 0, v_a_2653_);
lean_ctor_set(v___x_2664_, 1, v_location_x3f_2646_);
lean_ctor_set(v___x_2664_, 2, v_docString_x3f_2647_);
lean_ctor_set_uint8(v___x_2664_, sizeof(void*)*3, v_explicit_2648_);
v___x_2665_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
v___x_2666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2642_, v___x_2665_, v_infos_2659_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2666_);
v___x_2668_ = v___x_2662_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_steps_2658_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_holeIter_2660_);
v___x_2668_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = lean_st_ref_set(v_a_2649_, v___x_2668_);
v___x_2670_ = lean_box(0);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2670_);
v___x_2672_ = v___x_2655_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2677_, lean_object* v_stx_2678_, lean_object* v_e_2679_, lean_object* v_isBinder_2680_, lean_object* v_location_x3f_2681_, lean_object* v_docString_x3f_2682_, lean_object* v_explicit_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
uint8_t v_isBinder_boxed_2687_; uint8_t v_explicit_boxed_2688_; lean_object* v_res_2689_; 
v_isBinder_boxed_2687_ = lean_unbox(v_isBinder_2680_);
v_explicit_boxed_2688_ = lean_unbox(v_explicit_2683_);
v_res_2689_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2677_, v_stx_2678_, v_e_2679_, v_isBinder_boxed_2687_, v_location_x3f_2681_, v_docString_x3f_2682_, v_explicit_boxed_2688_, v_a_2684_, v_a_2685_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2690_, lean_object* v_stx_2691_, lean_object* v_e_2692_, uint8_t v_isBinder_2693_, lean_object* v_location_x3f_2694_, lean_object* v_docString_x3f_2695_, uint8_t v_explicit_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2690_, v_stx_2691_, v_e_2692_, v_isBinder_2693_, v_location_x3f_2694_, v_docString_x3f_2695_, v_explicit_2696_, v_a_2698_, v_a_2699_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2705_, lean_object* v_stx_2706_, lean_object* v_e_2707_, lean_object* v_isBinder_2708_, lean_object* v_location_x3f_2709_, lean_object* v_docString_x3f_2710_, lean_object* v_explicit_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_isBinder_boxed_2719_; uint8_t v_explicit_boxed_2720_; lean_object* v_res_2721_; 
v_isBinder_boxed_2719_ = lean_unbox(v_isBinder_2708_);
v_explicit_boxed_2720_ = lean_unbox(v_explicit_2711_);
v_res_2721_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2705_, v_stx_2706_, v_e_2707_, v_isBinder_boxed_2719_, v_location_x3f_2709_, v_docString_x3f_2710_, v_explicit_boxed_2720_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2731_; lean_object* v_a_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc_n(v_a_2728_, 2);
lean_dec_ref(v___x_2727_);
v___x_2729_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2723_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v___x_2731_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2723_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = 0;
v___x_2734_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2730_, v_a_2728_, v_a_2732_, v___x_2733_, v_a_2724_, v_a_2725_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v___x_2734_, 0);
lean_dec(v_unused_2742_);
v___x_2736_ = v___x_2734_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v___x_2734_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v_a_2728_);
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2728_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2728_);
v_a_2743_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2734_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2734_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
return v_res_2774_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2775_, lean_object* v_t_2776_){
_start:
{
if (lean_obj_tag(v_t_2776_) == 0)
{
lean_object* v_k_2777_; lean_object* v_l_2778_; lean_object* v_r_2779_; uint8_t v___x_2780_; 
v_k_2777_ = lean_ctor_get(v_t_2776_, 1);
v_l_2778_ = lean_ctor_get(v_t_2776_, 3);
v_r_2779_ = lean_ctor_get(v_t_2776_, 4);
v___x_2780_ = lean_nat_dec_lt(v_k_2775_, v_k_2777_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_eq(v_k_2775_, v_k_2777_);
if (v___x_2781_ == 0)
{
v_t_2776_ = v_r_2779_;
goto _start;
}
else
{
return v___x_2781_;
}
}
else
{
v_t_2776_ = v_l_2778_;
goto _start;
}
}
else
{
uint8_t v___x_2784_; 
v___x_2784_ = 0;
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2785_, lean_object* v_t_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2785_, v_t_2786_);
lean_dec(v_t_2786_);
lean_dec(v_k_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Syntax_getInfo_x3f(v_stx_2789_);
if (lean_obj_tag(v___x_2794_) == 1)
{
lean_object* v_val_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2814_; 
v_val_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2814_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_val_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2814_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
if (lean_obj_tag(v_val_2795_) == 1)
{
uint8_t v_canonical_2799_; 
v_canonical_2799_ = lean_ctor_get_uint8(v_val_2795_, sizeof(void*)*2);
if (v_canonical_2799_ == 0)
{
lean_object* v_pos_2800_; lean_object* v_endPos_2801_; lean_object* v___x_2802_; uint8_t v___y_2804_; uint8_t v___x_2809_; 
v_pos_2800_ = lean_ctor_get(v_val_2795_, 0);
lean_inc(v_pos_2800_);
v_endPos_2801_ = lean_ctor_get(v_val_2795_, 1);
lean_inc(v_endPos_2801_);
lean_dec_ref(v_val_2795_);
v___x_2802_ = lean_st_ref_get(v_a_2791_);
v___x_2809_ = lean_nat_dec_eq(v_pos_2800_, v_endPos_2801_);
lean_dec(v_endPos_2801_);
if (v___x_2809_ == 0)
{
lean_dec(v___x_2802_);
lean_dec(v_pos_2800_);
v___y_2804_ = v___x_2809_;
goto v___jp_2803_;
}
else
{
lean_object* v_infos_2810_; uint8_t v___x_2811_; 
v_infos_2810_ = lean_ctor_get(v___x_2802_, 1);
lean_inc(v_infos_2810_);
lean_dec(v___x_2802_);
v___x_2811_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2800_, v_infos_2810_);
lean_dec(v_infos_2810_);
lean_dec(v_pos_2800_);
v___y_2804_ = v___x_2811_;
goto v___jp_2803_;
}
v___jp_2803_:
{
if (v___y_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_del_object(v___x_2797_);
v___x_2805_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2805_;
}
else
{
lean_object* v___x_2807_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
lean_ctor_set(v___x_2797_, 0, v_stx_2789_);
v___x_2807_ = v___x_2797_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_stx_2789_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v___x_2812_; 
lean_dec_ref(v_val_2795_);
lean_del_object(v___x_2797_);
v___x_2812_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2812_;
}
}
else
{
lean_object* v___x_2813_; 
lean_del_object(v___x_2797_);
lean_dec(v_val_2795_);
v___x_2813_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2813_;
}
}
}
else
{
lean_object* v___x_2815_; 
lean_dec(v___x_2794_);
v___x_2815_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2839_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2840_, lean_object* v_k_2841_, lean_object* v_t_2842_){
_start:
{
uint8_t v___x_2843_; 
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2841_, v_t_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2844_, lean_object* v_k_2845_, lean_object* v_t_2846_){
_start:
{
uint8_t v_res_2847_; lean_object* v_r_2848_; 
v_res_2847_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2844_, v_k_2845_, v_t_2846_);
lean_dec(v_t_2846_);
lean_dec(v_k_2845_);
v_r_2848_ = lean_box(v_res_2847_);
return v_r_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; 
lean_inc(v_a_2855_);
lean_inc_ref(v_a_2854_);
lean_inc(v_a_2853_);
lean_inc_ref(v_a_2852_);
lean_inc(v_a_2851_);
lean_inc_ref(v_a_2850_);
v___x_2857_ = lean_apply_7(v_d_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, lean_box(0));
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2858_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_2859_;
}
else
{
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___x_2877_; 
lean_inc(v_a_2875_);
lean_inc_ref(v_a_2874_);
lean_inc(v_a_2873_);
lean_inc_ref(v_a_2872_);
lean_inc(v_a_2871_);
lean_inc_ref(v_a_2870_);
v___x_2877_ = lean_apply_7(v_d_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, lean_box(0));
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref(v___x_2877_);
v___x_2879_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2878_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2879_;
}
else
{
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
return v_res_2888_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2889_, lean_object* v_suggestion_x27_2890_, lean_object* v_x_2891_){
_start:
{
if (lean_obj_tag(v_x_2891_) == 1)
{
lean_object* v_fvarId_2892_; lean_object* v___x_2893_; 
v_fvarId_2892_ = lean_ctor_get(v_x_2891_, 0);
lean_inc(v_fvarId_2892_);
lean_dec_ref(v_x_2891_);
v___x_2893_ = lean_local_ctx_find(v_lctx_2889_, v_fvarId_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
uint8_t v___x_2894_; 
v___x_2894_ = 0;
return v___x_2894_;
}
else
{
lean_object* v_val_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_val_2895_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_val_2895_);
lean_dec_ref(v___x_2893_);
v___x_2896_ = l_Lean_LocalDecl_userName(v_val_2895_);
lean_dec(v_val_2895_);
v___x_2897_ = lean_name_eq(v___x_2896_, v_suggestion_x27_2890_);
lean_dec(v___x_2896_);
return v___x_2897_;
}
}
else
{
uint8_t v___x_2898_; 
lean_dec_ref(v_x_2891_);
lean_dec_ref(v_lctx_2889_);
v___x_2898_ = 0;
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2899_, lean_object* v_suggestion_x27_2900_, lean_object* v_x_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2899_, v_suggestion_x27_2900_, v_x_2901_);
lean_dec(v_suggestion_x27_2900_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2904_, lean_object* v_lctx_2905_, lean_object* v_suggestion_x27_2906_){
_start:
{
lean_object* v___f_2907_; lean_object* v___x_2908_; 
v___f_2907_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2907_, 0, v_lctx_2905_);
lean_closure_set(v___f_2907_, 1, v_suggestion_x27_2906_);
v___x_2908_ = lean_find_expr(v___f_2907_, v_body_2904_);
lean_dec_ref(v___f_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
uint8_t v___x_2909_; 
v___x_2909_ = 0;
return v___x_2909_;
}
else
{
uint8_t v___x_2910_; 
lean_dec_ref(v___x_2908_);
v___x_2910_ = 1;
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2911_, lean_object* v_lctx_2912_, lean_object* v_suggestion_x27_2913_){
_start:
{
uint8_t v_res_2914_; lean_object* v_r_2915_; 
v_res_2914_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2911_, v_lctx_2912_, v_suggestion_x27_2913_);
lean_dec_ref(v_body_2911_);
v_r_2915_ = lean_box(v_res_2914_);
return v_r_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_quotContext_2920_; lean_object* v_currMacroScope_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_quotContext_2920_ = lean_ctor_get(v___y_2917_, 10);
lean_inc(v_quotContext_2920_);
v_currMacroScope_2921_ = lean_ctor_get(v___y_2917_, 11);
lean_inc(v_currMacroScope_2921_);
lean_dec_ref(v___y_2917_);
v___x_2922_ = l_Lean_addMacroScope(v_quotContext_2920_, v_snd_2916_, v_currMacroScope_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_2933_, lean_object* v_body_2934_, uint8_t v_preserveName_2935_, lean_object* v_avoid_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; uint8_t v_fst_2976_; lean_object* v_snd_2977_; uint8_t v___x_2983_; 
v___x_2983_ = l_Lean_Name_isAnonymous(v_suggestion_2933_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_Name_hasMacroScopes(v_suggestion_2933_);
v___x_2985_ = lean_erase_macro_scopes(v_suggestion_2933_);
v_fst_2976_ = v___x_2984_;
v_snd_2977_ = v___x_2985_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_2986_; 
lean_dec(v_suggestion_2933_);
v___x_2986_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_2976_ = v___x_2983_;
v_snd_2977_ = v___x_2986_;
goto v___jp_2975_;
}
v___jp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = l_Lean_LocalContext_getUnusedName(v___y_2946_, v___y_2945_);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
v___jp_2949_:
{
if (v_preserveName_2935_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v___y_2952_);
v___x_2953_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_2954_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_2953_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2965_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2965_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2965_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_unbox(v_a_2955_);
lean_dec(v_a_2955_);
if (v___x_2959_ == 0)
{
lean_del_object(v___x_2957_);
v___y_2945_ = v___y_2950_;
v___y_2946_ = v___y_2951_;
goto v___jp_2944_;
}
else
{
uint8_t v___x_2960_; 
v___x_2960_ = l_Lean_NameSet_contains(v_avoid_2936_, v___y_2950_);
if (v___x_2960_ == 0)
{
uint8_t v___x_2961_; 
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2951_);
v___x_2961_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2934_, v___y_2951_, v___y_2950_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2963_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___y_2950_);
v___x_2963_ = v___x_2957_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___y_2950_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
else
{
lean_del_object(v___x_2957_);
v___y_2945_ = v___y_2950_;
v___y_2946_ = v___y_2951_;
goto v___jp_2944_;
}
}
else
{
lean_del_object(v___x_2957_);
v___y_2945_ = v___y_2950_;
v___y_2946_ = v___y_2951_;
goto v___jp_2944_;
}
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v___y_2950_);
v_a_2966_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2954_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2954_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
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
else
{
lean_object* v___x_2974_; 
lean_dec(v___y_2950_);
v___x_2974_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_2952_, v_a_2941_, v_a_2942_);
return v___x_2974_;
}
}
v___jp_2975_:
{
lean_object* v_lctx_2978_; uint8_t v___x_2979_; 
v_lctx_2978_ = lean_ctor_get(v_a_2939_, 2);
v___x_2979_ = l_Lean_LocalContext_usesUserName(v_lctx_2978_, v_snd_2977_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_snd_2977_);
return v___x_2980_;
}
else
{
lean_object* v___f_2981_; 
lean_inc(v_snd_2977_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2981_, 0, v_snd_2977_);
if (v_preserveName_2935_ == 0)
{
v___y_2950_ = v_snd_2977_;
v___y_2951_ = v_lctx_2978_;
v___y_2952_ = v___f_2981_;
goto v___jp_2949_;
}
else
{
if (v_fst_2976_ == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref(v___f_2981_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_snd_2977_);
return v___x_2982_;
}
else
{
v___y_2950_ = v_snd_2977_;
v___y_2951_ = v_lctx_2978_;
v___y_2952_ = v___f_2981_;
goto v___jp_2949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_2987_, lean_object* v_body_2988_, lean_object* v_preserveName_2989_, lean_object* v_avoid_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v_preserveName_boxed_2998_; lean_object* v_res_2999_; 
v_preserveName_boxed_2998_ = lean_unbox(v_preserveName_2989_);
v_res_2999_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_2987_, v_body_2988_, v_preserveName_boxed_2998_, v_avoid_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_avoid_2990_);
lean_dec_ref(v_body_2988_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3000_){
_start:
{
lean_object* v___x_3002_; lean_object* v_holeIter_3003_; lean_object* v_curr_3004_; lean_object* v___x_3005_; lean_object* v_steps_3006_; lean_object* v_infos_3007_; lean_object* v_holeIter_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3018_; 
v___x_3002_ = lean_st_ref_get(v___y_3000_);
v_holeIter_3003_ = lean_ctor_get(v___x_3002_, 2);
lean_inc_ref(v_holeIter_3003_);
lean_dec(v___x_3002_);
v_curr_3004_ = lean_ctor_get(v_holeIter_3003_, 0);
lean_inc(v_curr_3004_);
lean_dec_ref(v_holeIter_3003_);
v___x_3005_ = lean_st_ref_take(v___y_3000_);
v_steps_3006_ = lean_ctor_get(v___x_3005_, 0);
v_infos_3007_ = lean_ctor_get(v___x_3005_, 1);
v_holeIter_3008_ = lean_ctor_get(v___x_3005_, 2);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3010_ = v___x_3005_;
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_holeIter_3008_);
lean_inc(v_infos_3007_);
lean_inc(v_steps_3006_);
lean_dec(v___x_3005_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3008_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 2, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_steps_3006_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_infos_3007_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_st_ref_set(v___y_3000_, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_curr_3004_);
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3019_);
lean_dec(v___y_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3023_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3038_, lean_object* v_e_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3047_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3041_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_n(v_a_3048_, 2);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_mk_syntax_ident(v_n_3038_);
v___x_3050_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3048_, v___x_3049_);
v___x_3051_ = 0;
lean_inc(v___x_3050_);
v___x_3052_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3048_, v___x_3050_, v_e_3039_, v___x_3051_, v_a_3041_, v_a_3042_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3060_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3050_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v___x_3050_);
v_a_3061_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3052_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3052_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3069_, lean_object* v_e_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3069_, v_e_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3083_);
lean_inc(v___y_3082_);
lean_inc_ref(v___y_3081_);
v___x_3088_ = lean_apply_8(v_d_3079_, v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, lean_box(0));
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3089_, v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v_b_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3104_);
lean_inc_ref(v___y_3103_);
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
v___x_3108_ = lean_apply_8(v_k_3099_, v_b_3102_, v___y_3100_, v___y_3101_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, lean_box(0));
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3109_, v___y_3110_, v___y_3111_, v_b_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3119_, uint8_t v_bi_3120_, lean_object* v_type_3121_, lean_object* v_k_3122_, uint8_t v_kind_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___f_3131_; lean_object* v___x_3132_; 
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3131_, 0, v_k_3122_);
lean_closure_set(v___f_3131_, 1, v___y_3124_);
lean_closure_set(v___f_3131_, 2, v___y_3125_);
v___x_3132_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3119_, v_bi_3120_, v_type_3121_, v___f_3131_, v_kind_3123_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3132_) == 0)
{
return v___x_3132_;
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3141_, lean_object* v_bi_3142_, lean_object* v_type_3143_, lean_object* v_k_3144_, lean_object* v_kind_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v_bi_boxed_3153_; uint8_t v_kind_boxed_3154_; lean_object* v_res_3155_; 
v_bi_boxed_3153_ = lean_unbox(v_bi_3142_);
v_kind_boxed_3154_ = lean_unbox(v_kind_3145_);
v_res_3155_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3141_, v_bi_boxed_3153_, v_type_3143_, v_k_3144_, v_kind_boxed_3154_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3156_, lean_object* v_childIdx_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_subExpr_3166_; lean_object* v_optionsPerPos_3167_; lean_object* v_currNamespace_3168_; lean_object* v_openDecls_3169_; uint8_t v_inPattern_3170_; lean_object* v_depth_3171_; lean_object* v_pos_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_subExpr_3166_ = lean_ctor_get(v___y_3159_, 3);
v_optionsPerPos_3167_ = lean_ctor_get(v___y_3159_, 0);
v_currNamespace_3168_ = lean_ctor_get(v___y_3159_, 1);
v_openDecls_3169_ = lean_ctor_get(v___y_3159_, 2);
v_inPattern_3170_ = lean_ctor_get_uint8(v___y_3159_, sizeof(void*)*5);
v_depth_3171_ = lean_ctor_get(v___y_3159_, 4);
v_pos_3172_ = lean_ctor_get(v_subExpr_3166_, 1);
v___x_3173_ = l_Lean_SubExpr_Pos_push(v_pos_3172_, v_childIdx_3157_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_child_3156_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_inc(v_depth_3171_);
lean_inc(v_openDecls_3169_);
lean_inc(v_currNamespace_3168_);
lean_inc(v_optionsPerPos_3167_);
v___x_3175_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3175_, 0, v_optionsPerPos_3167_);
lean_ctor_set(v___x_3175_, 1, v_currNamespace_3168_);
lean_ctor_set(v___x_3175_, 2, v_openDecls_3169_);
lean_ctor_set(v___x_3175_, 3, v___x_3174_);
lean_ctor_set(v___x_3175_, 4, v_depth_3171_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*5, v_inPattern_3170_);
lean_inc(v___y_3164_);
lean_inc_ref(v___y_3163_);
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3160_);
v___x_3176_ = lean_apply_7(v_x_3158_, v___x_3175_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, lean_box(0));
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3177_, lean_object* v_childIdx_3178_, lean_object* v_x_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3177_, v_childIdx_3178_, v_x_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3188_, lean_object* v_a_3189_, lean_object* v_x_3190_, lean_object* v_fvar_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc_ref(v_fvar_3191_);
v___x_3199_ = lean_apply_8(v_v_3188_, v_fvar_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, lean_box(0));
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v___x_3201_ = l_Lean_Expr_bindingBody_x21(v_a_3189_);
v___x_3202_ = lean_expr_instantiate1(v___x_3201_, v_fvar_3191_);
lean_dec_ref(v_fvar_3191_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = lean_unsigned_to_nat(1u);
v___x_3204_ = lean_apply_1(v_x_3190_, v_a_3200_);
v___x_3205_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3202_, v___x_3203_, v___x_3204_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v_fvar_3191_);
lean_dec_ref(v_x_3190_);
v_a_3206_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3199_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3199_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3214_, lean_object* v_a_3215_, lean_object* v_x_3216_, lean_object* v_fvar_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3214_, v_a_3215_, v_x_3216_, v_fvar_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v_a_3215_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3226_, lean_object* v_v_3227_, lean_object* v_x_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; lean_object* v_a_3237_; lean_object* v___f_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3236_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3229_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc_n(v_a_3237_, 2);
lean_dec_ref(v___x_3236_);
v___f_3238_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3238_, 0, v_v_3227_);
lean_closure_set(v___f_3238_, 1, v_a_3237_);
lean_closure_set(v___f_3238_, 2, v_x_3228_);
v___x_3239_ = l_Lean_Expr_binderInfo(v_a_3237_);
v___x_3240_ = l_Lean_Expr_bindingDomain_x21(v_a_3237_);
lean_dec(v_a_3237_);
v___x_3241_ = 0;
v___x_3242_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3226_, v___x_3239_, v___x_3240_, v___f_3238_, v___x_3241_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3243_, lean_object* v_v_3244_, lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3243_, v_v_3244_, v_x_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3254_, uint8_t v_preserveName_3255_, lean_object* v_avoid_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v___x_3266_; lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3264_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3257_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3257_);
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = l_Lean_Expr_bindingName_x21(v_a_3265_);
lean_dec(v_a_3265_);
v___x_3269_ = l_Lean_Expr_bindingBody_x21(v_a_3267_);
lean_dec(v_a_3267_);
v___x_3270_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3268_, v___x_3269_, v_preserveName_3255_, v_avoid_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec_ref(v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___f_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc_n(v_a_3271_, 2);
lean_dec_ref(v___x_3270_);
v___f_3272_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3272_, 0, v_d_3254_);
v___x_3273_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3273_, 0, v_a_3271_);
v___x_3274_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3271_, v___x_3273_, v___f_3272_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
return v___x_3274_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v_d_3254_);
v_a_3275_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3270_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3283_, lean_object* v_preserveName_3284_, lean_object* v_avoid_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
uint8_t v_preserveName_boxed_3293_; lean_object* v_res_3294_; 
v_preserveName_boxed_3293_ = lean_unbox(v_preserveName_3284_);
v_res_3294_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3283_, v_preserveName_boxed_3293_, v_avoid_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_avoid_3285_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3295_, lean_object* v_d_3296_, uint8_t v_preserveName_3297_, lean_object* v_avoid_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3296_, v_preserveName_3297_, v_avoid_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3307_, lean_object* v_d_3308_, lean_object* v_preserveName_3309_, lean_object* v_avoid_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
uint8_t v_preserveName_boxed_3318_; lean_object* v_res_3319_; 
v_preserveName_boxed_3318_ = lean_unbox(v_preserveName_3309_);
v_res_3319_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3307_, v_d_3308_, v_preserveName_boxed_3318_, v_avoid_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_avoid_3310_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3320_, lean_object* v_child_3321_, lean_object* v_childIdx_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3321_, v_childIdx_3322_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3332_, lean_object* v_child_3333_, lean_object* v_childIdx_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3332_, v_child_3333_, v_childIdx_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3344_, lean_object* v_name_3345_, uint8_t v_bi_3346_, lean_object* v_type_3347_, lean_object* v_k_3348_, uint8_t v_kind_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3345_, v_bi_3346_, v_type_3347_, v_k_3348_, v_kind_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3358_, lean_object* v_name_3359_, lean_object* v_bi_3360_, lean_object* v_type_3361_, lean_object* v_k_3362_, lean_object* v_kind_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
uint8_t v_bi_boxed_3371_; uint8_t v_kind_boxed_3372_; lean_object* v_res_3373_; 
v_bi_boxed_3371_ = lean_unbox(v_bi_3360_);
v_kind_boxed_3372_ = lean_unbox(v_kind_3363_);
v_res_3373_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3358_, v_name_3359_, v_bi_boxed_3371_, v_type_3361_, v_k_3362_, v_kind_boxed_3372_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3374_, lean_object* v_00_u03b2_3375_, lean_object* v_n_3376_, lean_object* v_v_3377_, lean_object* v_x_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3376_, v_v_3377_, v_x_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3387_, lean_object* v_00_u03b2_3388_, lean_object* v_n_3389_, lean_object* v_v_3390_, lean_object* v_x_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3387_, v_00_u03b2_3388_, v_n_3389_, v_v_3390_, v_x_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object* v_x_3400_){
_start:
{
switch(lean_obj_tag(v_x_3400_))
{
case 0:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_unsigned_to_nat(0u);
return v___x_3401_;
}
case 1:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_unsigned_to_nat(1u);
return v___x_3402_;
}
case 2:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_unsigned_to_nat(2u);
return v___x_3403_;
}
default: 
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_unsigned_to_nat(3u);
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object* v_x_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(v_x_3405_);
lean_dec(v_x_3405_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3407_, lean_object* v_k_3408_){
_start:
{
if (lean_obj_tag(v_t_3407_) == 3)
{
lean_object* v_s_3409_; lean_object* v___x_3410_; 
v_s_3409_ = lean_ctor_get(v_t_3407_, 0);
lean_inc_ref(v_s_3409_);
lean_dec_ref(v_t_3407_);
v___x_3410_ = lean_apply_1(v_k_3408_, v_s_3409_);
return v___x_3410_;
}
else
{
lean_dec(v_t_3407_);
return v_k_3408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3411_, lean_object* v_ctorIdx_3412_, lean_object* v_t_3413_, lean_object* v_h_3414_, lean_object* v_k_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3413_, v_k_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3417_, lean_object* v_ctorIdx_3418_, lean_object* v_t_3419_, lean_object* v_h_3420_, lean_object* v_k_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3417_, v_ctorIdx_3418_, v_t_3419_, v_h_3420_, v_k_3421_);
lean_dec(v_ctorIdx_3418_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3423_, lean_object* v_deep_3424_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3423_, v_deep_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3426_, lean_object* v_t_3427_, lean_object* v_h_3428_, lean_object* v_deep_3429_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3427_, v_deep_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3431_, lean_object* v_proof_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3431_, v_proof_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3434_, lean_object* v_t_3435_, lean_object* v_h_3436_, lean_object* v_proof_3437_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3435_, v_proof_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3439_, lean_object* v_maxSteps_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3439_, v_maxSteps_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3442_, lean_object* v_t_3443_, lean_object* v_h_3444_, lean_object* v_maxSteps_3445_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3443_, v_maxSteps_3445_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3447_, lean_object* v_string_3448_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3447_, v_string_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3450_, lean_object* v_t_3451_, lean_object* v_h_3452_, lean_object* v_string_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3451_, v_string_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3458_){
_start:
{
switch(lean_obj_tag(v_x_3458_))
{
case 0:
{
lean_object* v___x_3459_; 
v___x_3459_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3459_;
}
case 1:
{
lean_object* v___x_3460_; 
v___x_3460_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3460_;
}
case 2:
{
lean_object* v___x_3461_; 
v___x_3461_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3461_;
}
default: 
{
lean_object* v_s_3462_; 
v_s_3462_ = lean_ctor_get(v_x_3458_, 0);
lean_inc_ref(v_s_3462_);
return v_s_3462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3463_);
lean_dec(v_x_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3465_, lean_object* v_stx_3466_, lean_object* v_e_3467_, lean_object* v_reason_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3472_ = 0;
v___x_3473_ = lean_box(0);
v___x_3474_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3468_);
v___x_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
v___x_3476_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3465_, v_stx_3466_, v_e_3467_, v___x_3472_, v___x_3473_, v___x_3475_, v___x_3472_, v_a_3469_, v_a_3470_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3477_, lean_object* v_stx_3478_, lean_object* v_e_3479_, lean_object* v_reason_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3477_, v_stx_3478_, v_e_3479_, v_reason_3480_, v_a_3481_, v_a_3482_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec(v_reason_3480_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3485_, lean_object* v_stx_3486_, lean_object* v_e_3487_, lean_object* v_reason_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3485_, v_stx_3486_, v_e_3487_, v_reason_3488_, v_a_3490_, v_a_3491_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3497_, lean_object* v_stx_3498_, lean_object* v_e_3499_, lean_object* v_reason_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3497_, v_stx_3498_, v_e_3499_, v_reason_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_reason_3500_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3509_, lean_object* v_ctx_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_optionsPerPos_3517_; lean_object* v_currNamespace_3518_; lean_object* v_openDecls_3519_; uint8_t v_inPattern_3520_; lean_object* v_subExpr_3521_; lean_object* v_depth_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_optionsPerPos_3517_ = lean_ctor_get(v_ctx_3510_, 0);
v_currNamespace_3518_ = lean_ctor_get(v_ctx_3510_, 1);
v_openDecls_3519_ = lean_ctor_get(v_ctx_3510_, 2);
v_inPattern_3520_ = lean_ctor_get_uint8(v_ctx_3510_, sizeof(void*)*5);
v_subExpr_3521_ = lean_ctor_get(v_ctx_3510_, 3);
v_depth_3522_ = lean_ctor_get(v_ctx_3510_, 4);
v___x_3523_ = lean_unsigned_to_nat(1u);
v___x_3524_ = lean_nat_add(v_depth_3522_, v___x_3523_);
lean_inc_ref(v_subExpr_3521_);
lean_inc(v_openDecls_3519_);
lean_inc(v_currNamespace_3518_);
lean_inc(v_optionsPerPos_3517_);
v___x_3525_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3525_, 0, v_optionsPerPos_3517_);
lean_ctor_set(v___x_3525_, 1, v_currNamespace_3518_);
lean_ctor_set(v___x_3525_, 2, v_openDecls_3519_);
lean_ctor_set(v___x_3525_, 3, v_subExpr_3521_);
lean_ctor_set(v___x_3525_, 4, v___x_3524_);
lean_ctor_set_uint8(v___x_3525_, sizeof(void*)*5, v_inPattern_3520_);
lean_inc(v_a_3515_);
lean_inc_ref(v_a_3514_);
lean_inc(v_a_3513_);
lean_inc_ref(v_a_3512_);
lean_inc(v_a_3511_);
v___x_3526_ = lean_apply_7(v_act_3509_, v___x_3525_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, lean_box(0));
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3527_, lean_object* v_ctx_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3527_, v_ctx_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_ctx_3528_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3536_, lean_object* v_act_3537_, lean_object* v_ctx_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3537_, v_ctx_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_act_3547_, lean_object* v_ctx_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3546_, v_act_3547_, v_ctx_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_ctx_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3556_, lean_object* v_e_3557_){
_start:
{
lean_object* v___y_3559_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3563_ = lean_unsigned_to_nat(254u);
v___x_3564_ = lean_nat_dec_le(v___x_3563_, v_threshold_3556_);
if (v___x_3564_ == 0)
{
v___y_3559_ = v_threshold_3556_;
goto v___jp_3558_;
}
else
{
v___y_3559_ = v___x_3563_;
goto v___jp_3558_;
}
v___jp_3558_:
{
uint32_t v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = l_Lean_Expr_approxDepth(v_e_3557_);
v___x_3561_ = lean_uint32_to_nat(v___x_3560_);
v___x_3562_ = lean_nat_dec_le(v___x_3561_, v___y_3559_);
lean_dec(v___x_3561_);
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3565_, lean_object* v_e_3566_){
_start:
{
uint8_t v_res_3567_; lean_object* v_r_3568_; 
v_res_3567_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3565_, v_e_3566_);
lean_dec_ref(v_e_3566_);
lean_dec(v_threshold_3565_);
v_r_3568_ = lean_box(v_res_3567_);
return v_r_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_Expr_isAtomic(v_e_3571_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3581_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3580_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3625_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3625_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3625_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_unbox(v_a_3582_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_del_object(v___x_3584_);
v___x_3587_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3588_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3587_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3612_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3612_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3612_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_depth_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_depth_3593_ = lean_ctor_get(v_a_3572_, 4);
v___x_3594_ = lean_nat_sub(v_depth_3593_, v_a_3589_);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_nat_dec_lt(v___x_3595_, v___x_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
lean_dec(v___x_3594_);
lean_dec(v_a_3589_);
lean_dec(v_a_3582_);
v___x_3597_ = lean_box(v___x_3596_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3597_);
v___x_3599_ = v___x_3591_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3601_ = lean_unsigned_to_nat(2u);
v___x_3602_ = lean_nat_shiftr(v_a_3589_, v___x_3601_);
lean_dec(v_a_3589_);
v___x_3603_ = lean_nat_sub(v___x_3602_, v___x_3594_);
lean_dec(v___x_3594_);
lean_dec(v___x_3602_);
v___x_3604_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3603_, v_e_3571_);
lean_dec(v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_dec(v_a_3582_);
v___x_3605_ = lean_box(v___x_3596_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3605_);
v___x_3607_ = v___x_3591_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
else
{
lean_object* v___x_3610_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v_a_3582_);
v___x_3610_ = v___x_3591_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3582_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_a_3582_);
v_a_3613_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3588_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3588_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3623_; 
lean_dec(v_a_3582_);
v___x_3621_ = lean_box(v___x_3579_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3621_);
v___x_3623_ = v___x_3584_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
return v___x_3581_;
}
}
else
{
uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = 0;
v___x_3627_ = lean_box(v___x_3626_);
v___x_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec_ref(v_e_3629_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = l_Lean_Expr_isAtomic(v_e_3640_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3650_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3649_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3701_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___y_3656_; uint8_t v___x_3681_; 
v___x_3681_ = lean_unbox(v_a_3651_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_del_object(v___x_3653_);
lean_inc_ref(v_e_3640_);
v___x_3682_ = l_Lean_Meta_isProof(v_e_3640_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
if (lean_obj_tag(v___x_3682_) == 0)
{
v___y_3656_ = v___x_3682_;
goto v___jp_3655_;
}
else
{
lean_object* v_a_3683_; uint8_t v___y_3685_; uint8_t v___x_3695_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
v___x_3695_ = l_Lean_Exception_isInterrupt(v_a_3683_);
if (v___x_3695_ == 0)
{
uint8_t v___x_3696_; 
v___x_3696_ = l_Lean_Exception_isRuntime(v_a_3683_);
v___y_3685_ = v___x_3696_;
goto v___jp_3684_;
}
else
{
lean_dec(v_a_3683_);
v___y_3685_ = v___x_3695_;
goto v___jp_3684_;
}
v___jp_3684_:
{
if (v___y_3685_ == 0)
{
lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_a_3651_);
lean_dec_ref(v_e_3640_);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v___x_3682_, 0);
lean_dec(v_unused_3694_);
v___x_3687_ = v___x_3682_;
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
else
{
lean_dec(v___x_3682_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_box(v___y_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3689_);
v___x_3691_ = v___x_3687_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
else
{
v___y_3656_ = v___x_3682_;
goto v___jp_3655_;
}
}
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3699_; 
lean_dec(v_a_3651_);
lean_dec_ref(v_e_3640_);
v___x_3697_ = lean_box(v___x_3648_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3697_);
v___x_3699_ = v___x_3653_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
v___jp_3655_:
{
if (lean_obj_tag(v___y_3656_) == 0)
{
lean_object* v_a_3657_; uint8_t v___x_3658_; 
v_a_3657_ = lean_ctor_get(v___y_3656_, 0);
v___x_3658_ = lean_unbox(v_a_3657_);
if (v___x_3658_ == 0)
{
lean_dec(v_a_3651_);
lean_dec_ref(v_e_3640_);
return v___y_3656_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_inc(v_a_3657_);
lean_dec_ref(v___y_3656_);
v___x_3659_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3660_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3659_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3672_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3672_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3672_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
uint8_t v___x_3665_; 
v___x_3665_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3661_, v_e_3640_);
lean_dec_ref(v_e_3640_);
lean_dec(v_a_3661_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3667_; 
lean_dec(v_a_3651_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v_a_3657_);
v___x_3667_ = v___x_3663_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3657_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
else
{
lean_object* v___x_3670_; 
lean_dec(v_a_3657_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v_a_3651_);
v___x_3670_ = v___x_3663_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3651_);
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
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3657_);
lean_dec(v_a_3651_);
lean_dec_ref(v_e_3640_);
v_a_3673_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3660_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3660_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
else
{
lean_dec(v_a_3651_);
lean_dec_ref(v_e_3640_);
return v___y_3656_;
}
}
}
}
else
{
lean_dec_ref(v_e_3640_);
return v___x_3650_;
}
}
else
{
uint8_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec_ref(v_e_3640_);
v___x_3702_ = 0;
v___x_3703_ = lean_box(v___x_3702_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v_ref_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v_ref_3728_ = lean_ctor_get(v_a_3726_, 5);
v___x_3729_ = 0;
v___x_3730_ = l_Lean_SourceInfo_fromRef(v_ref_3728_, v___x_3729_);
v___x_3731_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3732_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3730_);
v___x_3733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3730_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_Syntax_node1(v___x_3730_, v___x_3731_, v___x_3733_);
v___x_3735_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3734_, v_a_3723_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v_a_3740_; lean_object* v___x_3741_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc_n(v_a_3736_, 2);
lean_dec_ref(v___x_3735_);
v___x_3737_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3723_);
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3723_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3739_);
v___x_3741_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3738_, v_a_3736_, v_a_3740_, v_reason_3722_, v_a_3724_, v_a_3725_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3749_);
v___x_3743_ = v___x_3741_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v_a_3736_);
v___x_3746_ = v___x_3743_;
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
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_a_3736_);
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
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
return v___x_3735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
lean_dec_ref(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_reason_3758_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3770_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_reason_3774_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 0)
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3791_;
}
else
{
lean_object* v_head_3792_; lean_object* v_tail_3793_; lean_object* v___x_3794_; 
v_head_3792_ = lean_ctor_get(v_x_3783_, 0);
lean_inc(v_head_3792_);
v_tail_3793_ = lean_ctor_get(v_x_3783_, 1);
lean_inc(v_tail_3793_);
lean_dec_ref(v_x_3783_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
lean_inc(v___y_3785_);
lean_inc_ref(v___y_3784_);
v___x_3794_ = lean_apply_7(v_head_3792_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, lean_box(0));
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_dec(v_tail_3793_);
return v___x_3794_;
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3796_; uint8_t v___y_3798_; uint8_t v___x_3802_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
v___x_3796_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3802_ = l_Lean_Exception_isInterrupt(v_a_3795_);
if (v___x_3802_ == 0)
{
uint8_t v___x_3803_; 
lean_inc(v_a_3795_);
v___x_3803_ = l_Lean_Exception_isRuntime(v_a_3795_);
v___y_3798_ = v___x_3803_;
goto v___jp_3797_;
}
else
{
v___y_3798_ = v___x_3802_;
goto v___jp_3797_;
}
v___jp_3797_:
{
if (v___y_3798_ == 0)
{
if (lean_obj_tag(v_a_3795_) == 0)
{
lean_dec_ref(v_a_3795_);
lean_dec(v_tail_3793_);
return v___x_3794_;
}
else
{
lean_object* v_id_3799_; uint8_t v___x_3800_; 
v_id_3799_ = lean_ctor_get(v_a_3795_, 0);
lean_inc(v_id_3799_);
lean_dec_ref(v_a_3795_);
v___x_3800_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3796_, v_id_3799_);
lean_dec(v_id_3799_);
if (v___x_3800_ == 0)
{
lean_dec(v_tail_3793_);
return v___x_3794_;
}
else
{
lean_dec_ref(v___x_3794_);
v_x_3783_ = v_tail_3793_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3795_);
lean_dec(v_tail_3793_);
return v___x_3794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; uint8_t v___y_3825_; lean_object* v___y_3833_; 
if (lean_obj_tag(v_x_3813_) == 0)
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; lean_object* v_env_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3839_ = lean_st_ref_get(v_a_3819_);
v_env_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref(v_env_3840_);
lean_dec(v___x_3839_);
v___x_3841_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3842_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3841_, v_env_3840_, v_x_3813_);
v___x_3843_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3842_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3845_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3844_, v_a_3814_, v_a_3815_, v_a_3816_);
v___y_3833_ = v___x_3845_;
goto v___jp_3832_;
}
else
{
v___y_3833_ = v___x_3843_;
goto v___jp_3832_;
}
}
v___jp_3821_:
{
if (v___y_3825_ == 0)
{
if (lean_obj_tag(v___y_3822_) == 0)
{
lean_dec_ref(v___y_3822_);
lean_dec(v_x_3813_);
return v___y_3823_;
}
else
{
lean_object* v_id_3826_; uint8_t v___x_3827_; 
v_id_3826_ = lean_ctor_get(v___y_3822_, 0);
lean_inc(v_id_3826_);
lean_dec_ref(v___y_3822_);
v___x_3827_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3824_, v_id_3826_);
lean_dec(v_id_3826_);
if (v___x_3827_ == 0)
{
lean_dec(v_x_3813_);
return v___y_3823_;
}
else
{
uint8_t v___x_3828_; 
lean_dec_ref(v___y_3823_);
v___x_3828_ = l_Lean_Name_isAtomic(v_x_3813_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_Name_getRoot(v_x_3813_);
lean_dec(v_x_3813_);
v_x_3813_ = v___x_3829_;
goto _start;
}
else
{
lean_object* v___x_3831_; 
lean_dec(v_x_3813_);
v___x_3831_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3831_;
}
}
}
}
else
{
lean_dec_ref(v___y_3822_);
lean_dec(v_x_3813_);
return v___y_3823_;
}
}
v___jp_3832_:
{
if (lean_obj_tag(v___y_3833_) == 0)
{
lean_dec(v_x_3813_);
return v___y_3833_;
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_a_3834_ = lean_ctor_get(v___y_3833_, 0);
lean_inc(v_a_3834_);
v___x_3835_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3836_ = l_Lean_Exception_isInterrupt(v_a_3834_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
lean_inc(v_a_3834_);
v___x_3837_ = l_Lean_Exception_isRuntime(v_a_3834_);
v___y_3822_ = v_a_3834_;
v___y_3823_ = v___y_3833_;
v___y_3824_ = v___x_3835_;
v___y_3825_ = v___x_3837_;
goto v___jp_3821_;
}
else
{
v___y_3822_ = v_a_3834_;
v___y_3823_ = v___y_3833_;
v___y_3824_ = v___x_3835_;
v___y_3825_ = v___x_3836_;
goto v___jp_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; lean_object* v_env_3862_; lean_object* v___x_3863_; lean_object* v_mctx_3864_; lean_object* v_lctx_3865_; lean_object* v_options_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3861_ = lean_st_ref_get(v___y_3859_);
v_env_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc_ref(v_env_3862_);
lean_dec(v___x_3861_);
v___x_3863_ = lean_st_ref_get(v___y_3857_);
v_mctx_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc_ref(v_mctx_3864_);
lean_dec(v___x_3863_);
v_lctx_3865_ = lean_ctor_get(v___y_3856_, 2);
v_options_3866_ = lean_ctor_get(v___y_3858_, 2);
lean_inc_ref(v_options_3866_);
lean_inc_ref(v_lctx_3865_);
v___x_3867_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3867_, 0, v_env_3862_);
lean_ctor_set(v___x_3867_, 1, v_mctx_3864_);
lean_ctor_set(v___x_3867_, 2, v_lctx_3865_);
lean_ctor_set(v___x_3867_, 3, v_options_3866_);
v___x_3868_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v_msgData_3855_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_ref_3883_; lean_object* v___x_3884_; lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3893_; 
v_ref_3883_ = lean_ctor_get(v___y_3880_, 5);
v___x_3884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3893_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3893_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v___x_3891_; 
lean_inc(v_ref_3883_);
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_ref_3883_);
lean_ctor_set(v___x_3889_, 1, v_a_3885_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set_tag(v___x_3887_, 1);
lean_ctor_set(v___x_3887_, 0, v___x_3889_);
v___x_3891_ = v___x_3887_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3900_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3903_ = l_Lean_stringToMessageData(v___x_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; 
lean_inc(v_a_3904_);
v___x_3912_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_dec(v_a_3904_);
return v___x_3912_;
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3914_; uint8_t v___y_3916_; uint8_t v___x_3932_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
v___x_3914_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3932_ = l_Lean_Exception_isInterrupt(v_a_3913_);
if (v___x_3932_ == 0)
{
uint8_t v___x_3933_; 
lean_inc(v_a_3913_);
v___x_3933_ = l_Lean_Exception_isRuntime(v_a_3913_);
v___y_3916_ = v___x_3933_;
goto v___jp_3915_;
}
else
{
v___y_3916_ = v___x_3932_;
goto v___jp_3915_;
}
v___jp_3915_:
{
if (v___y_3916_ == 0)
{
if (lean_obj_tag(v_a_3913_) == 0)
{
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3904_);
return v___x_3912_;
}
else
{
lean_object* v_id_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3930_; 
v_id_3917_ = lean_ctor_get(v_a_3913_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3913_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v_a_3913_, 1);
lean_dec(v_unused_3931_);
v___x_3919_ = v_a_3913_;
v_isShared_3920_ = v_isSharedCheck_3930_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_id_3917_);
lean_dec(v_a_3913_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3930_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3914_, v_id_3917_);
lean_dec(v_id_3917_);
if (v___x_3921_ == 0)
{
lean_del_object(v___x_3919_);
lean_dec(v_a_3904_);
return v___x_3912_;
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_dec_ref(v___x_3912_);
v___x_3922_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_3923_ = l_Lean_MessageData_ofName(v_a_3904_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set_tag(v___x_3919_, 7);
lean_ctor_set(v___x_3919_, 1, v___x_3923_);
lean_ctor_set(v___x_3919_, 0, v___x_3922_);
v___x_3925_ = v___x_3919_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__11_spec__15___redArg___closed__3);
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3925_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_3927_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
return v___x_3928_;
}
}
}
}
}
else
{
lean_dec(v_a_3913_);
lean_dec(v_a_3904_);
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; lean_object* v_a_3952_; lean_object* v___x_3953_; 
v___x_3951_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3944_);
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
lean_inc(v___y_3949_);
lean_inc_ref(v___y_3948_);
lean_inc(v___y_3947_);
lean_inc_ref(v___y_3946_);
v___x_3953_ = lean_infer_type(v_a_3952_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3953_);
v___x_3955_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_3956_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_3954_, v___x_3955_, v_x_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v_x_3943_);
v_a_3957_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3953_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3953_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
return v_res_3973_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_3992_ = l_String_toRawSubstring_x27(v___x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_4051_ = l_Lean_Core_checkSystem(v___x_4050_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec_ref(v___x_4051_);
v___x_4052_ = lean_st_ref_get(v_a_4044_);
v___x_4053_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4054_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4053_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v_steps_4056_; uint8_t v___x_4057_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref(v___x_4054_);
v_steps_4056_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_steps_4056_);
lean_dec(v___x_4052_);
v___x_4057_ = lean_nat_dec_le(v_a_4055_, v_steps_4056_);
lean_dec(v_steps_4056_);
lean_dec(v_a_4055_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v_steps_4059_; lean_object* v_infos_4060_; lean_object* v_holeIter_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4232_; 
v___x_4058_ = lean_st_ref_take(v_a_4044_);
v_steps_4059_ = lean_ctor_get(v___x_4058_, 0);
v_infos_4060_ = lean_ctor_get(v___x_4058_, 1);
v_holeIter_4061_ = lean_ctor_get(v___x_4058_, 2);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4063_ = v___x_4058_;
v_isShared_4064_ = v_isSharedCheck_4232_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_holeIter_4061_);
lean_inc(v_infos_4060_);
lean_inc(v_steps_4059_);
lean_dec(v___x_4058_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4232_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_nat_add(v_steps_4059_, v___x_4065_);
lean_dec(v_steps_4059_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4066_);
v___x_4068_ = v___x_4063_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_infos_4060_);
lean_ctor_set(v_reuseFailAlloc_4231_, 2, v_holeIter_4061_);
v___x_4068_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = lean_st_ref_set(v_a_4044_, v___x_4068_);
v___x_4070_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4043_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref(v___x_4070_);
v___x_4072_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4071_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; uint8_t v___x_4074_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
v___x_4074_ = lean_unbox(v_a_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; 
lean_inc(v_a_4071_);
v___x_4075_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4071_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; uint8_t v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref(v___x_4075_);
v___x_4077_ = lean_unbox(v_a_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
lean_dec(v_a_4073_);
v___x_4078_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___f_4080_; lean_object* v___x_4081_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref(v___x_4078_);
v___f_4080_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4080_, 0, v_a_4079_);
v___x_4081_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4080_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___y_4084_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4081_);
v___x_4130_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4131_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4130_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; uint8_t v___x_4133_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
v___x_4133_ = lean_unbox(v_a_4132_);
lean_dec(v_a_4132_);
if (v___x_4133_ == 0)
{
lean_dec(v_a_4071_);
v___y_4084_ = v___x_4131_;
goto v___jp_4083_;
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v___x_4131_);
v___x_4134_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4135_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4134_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; uint8_t v___x_4137_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
v___x_4137_ = lean_unbox(v_a_4136_);
lean_dec(v_a_4136_);
if (v___x_4137_ == 0)
{
lean_dec(v_a_4071_);
v___y_4084_ = v___x_4135_;
goto v___jp_4083_;
}
else
{
uint8_t v___x_4138_; 
v___x_4138_ = l_Lean_Expr_isMData(v_a_4071_);
lean_dec(v_a_4071_);
if (v___x_4138_ == 0)
{
v___y_4084_ = v___x_4135_;
goto v___jp_4083_;
}
else
{
lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v_a_4076_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; 
v_unused_4146_ = lean_ctor_get(v___x_4135_, 0);
lean_dec(v_unused_4146_);
v___x_4140_ = v___x_4135_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_dec(v___x_4135_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v_a_4082_);
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4082_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
else
{
lean_dec(v_a_4071_);
v___y_4084_ = v___x_4135_;
goto v___jp_4083_;
}
}
}
else
{
lean_dec(v_a_4071_);
v___y_4084_ = v___x_4131_;
goto v___jp_4083_;
}
v___jp_4083_:
{
if (lean_obj_tag(v___y_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4121_; 
v_a_4085_ = lean_ctor_get(v___y_4084_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___y_4084_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4087_ = v___y_4084_;
v_isShared_4088_ = v_isSharedCheck_4121_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___y_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4121_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
uint8_t v___x_4089_; 
v___x_4089_ = lean_unbox(v_a_4085_);
lean_dec(v_a_4085_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4091_; 
lean_dec(v_a_4076_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_a_4082_);
v___x_4091_ = v___x_4087_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4082_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
else
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_del_object(v___x_4087_);
v___x_4093_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4094_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4093_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v_ref_4096_; lean_object* v_quotContext_4097_; lean_object* v_currMacroScope_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref(v___x_4094_);
v_ref_4096_ = lean_ctor_get(v_a_4047_, 5);
v_quotContext_4097_ = lean_ctor_get(v_a_4047_, 10);
v_currMacroScope_4098_ = lean_ctor_get(v_a_4047_, 11);
v___x_4099_ = lean_unbox(v_a_4076_);
lean_dec(v_a_4076_);
v___x_4100_ = l_Lean_SourceInfo_fromRef(v_ref_4096_, v___x_4099_);
v___x_4101_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4102_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4103_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4100_, 7);
v___x_4104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4100_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4106_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4107_ = lean_box(0);
lean_inc(v_currMacroScope_4098_);
lean_inc(v_quotContext_4097_);
v___x_4108_ = l_Lean_addMacroScope(v_quotContext_4097_, v___x_4107_, v_currMacroScope_4098_);
v___x_4109_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4100_);
lean_ctor_set(v___x_4110_, 1, v___x_4106_);
lean_ctor_set(v___x_4110_, 2, v___x_4108_);
lean_ctor_set(v___x_4110_, 3, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node1(v___x_4100_, v___x_4105_, v___x_4110_);
v___x_4112_ = l_Lean_Syntax_node2(v___x_4100_, v___x_4102_, v___x_4104_, v___x_4111_);
v___x_4113_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4100_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_4116_ = l_Lean_Syntax_node1(v___x_4100_, v___x_4115_, v_a_4095_);
v___x_4117_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4100_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = l_Lean_Syntax_node5(v___x_4100_, v___x_4101_, v___x_4112_, v_a_4082_, v___x_4114_, v___x_4116_, v___x_4118_);
v___x_4120_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4119_, v_a_4043_);
return v___x_4120_;
}
else
{
lean_dec(v_a_4082_);
lean_dec(v_a_4076_);
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_a_4082_);
lean_dec(v_a_4076_);
v_a_4122_ = lean_ctor_get(v___y_4084_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___y_4084_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___y_4084_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___y_4084_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
else
{
lean_dec(v_a_4076_);
lean_dec(v_a_4071_);
return v___x_4081_;
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_a_4076_);
lean_dec(v_a_4071_);
v_a_4147_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4078_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4078_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec(v_a_4076_);
lean_dec(v_a_4071_);
v___x_4155_ = lean_box(1);
v___x_4156_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4155_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4047_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref(v___x_4156_);
v___x_4158_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4159_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4158_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4196_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4162_ = v___x_4159_;
v_isShared_4163_ = v_isSharedCheck_4196_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4196_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
uint8_t v___x_4164_; 
v___x_4164_ = lean_unbox(v_a_4160_);
lean_dec(v_a_4160_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v_a_4073_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v_a_4157_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4157_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_del_object(v___x_4162_);
v___x_4168_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4169_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4168_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v_ref_4171_; lean_object* v_quotContext_4172_; lean_object* v_currMacroScope_4173_; uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref(v___x_4169_);
v_ref_4171_ = lean_ctor_get(v_a_4047_, 5);
v_quotContext_4172_ = lean_ctor_get(v_a_4047_, 10);
v_currMacroScope_4173_ = lean_ctor_get(v_a_4047_, 11);
v___x_4174_ = lean_unbox(v_a_4073_);
lean_dec(v_a_4073_);
v___x_4175_ = l_Lean_SourceInfo_fromRef(v_ref_4171_, v___x_4174_);
v___x_4176_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4177_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4178_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4175_, 7);
v___x_4179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4175_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4181_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4182_ = lean_box(0);
lean_inc(v_currMacroScope_4173_);
lean_inc(v_quotContext_4172_);
v___x_4183_ = l_Lean_addMacroScope(v_quotContext_4172_, v___x_4182_, v_currMacroScope_4173_);
v___x_4184_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4185_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4175_);
lean_ctor_set(v___x_4185_, 1, v___x_4181_);
lean_ctor_set(v___x_4185_, 2, v___x_4183_);
lean_ctor_set(v___x_4185_, 3, v___x_4184_);
v___x_4186_ = l_Lean_Syntax_node1(v___x_4175_, v___x_4180_, v___x_4185_);
v___x_4187_ = l_Lean_Syntax_node2(v___x_4175_, v___x_4177_, v___x_4179_, v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4175_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_4191_ = l_Lean_Syntax_node1(v___x_4175_, v___x_4190_, v_a_4170_);
v___x_4192_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4175_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = l_Lean_Syntax_node5(v___x_4175_, v___x_4176_, v___x_4187_, v_a_4157_, v___x_4189_, v___x_4191_, v___x_4193_);
v___x_4195_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4194_, v_a_4043_);
return v___x_4195_;
}
else
{
lean_dec(v_a_4157_);
lean_dec(v_a_4073_);
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_a_4157_);
lean_dec(v_a_4073_);
v_a_4197_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4159_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4159_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
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
else
{
lean_dec(v_a_4073_);
return v___x_4156_;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec(v_a_4073_);
lean_dec(v_a_4071_);
v_a_4205_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4075_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4075_);
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
lean_dec(v_a_4073_);
lean_dec(v_a_4071_);
v___x_4213_ = lean_box(0);
v___x_4214_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4213_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4047_);
return v___x_4214_;
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v_a_4071_);
v_a_4215_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4072_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4072_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4070_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4070_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
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
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_box(2);
v___x_4234_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4233_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4047_);
return v___x_4234_;
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v___x_4052_);
v_a_4235_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4054_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4054_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4243_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4051_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4051_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4251_, lean_object* v_msg_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4259_, lean_object* v_msg_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4259_, v_msg_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4277_, v_x_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4288_, lean_object* v_prec_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4298_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4297_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4311_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4311_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4311_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4303_; lean_object* v_mctx_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4303_ = lean_st_ref_get(v_a_4293_);
v_mctx_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc_ref(v_mctx_4304_);
lean_dec(v___x_4303_);
v___x_4305_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4305_, 0, v_mctx_4304_);
v___x_4306_ = lean_unbox(v_a_4299_);
lean_dec(v_a_4299_);
v___x_4307_ = l_Lean_Level_quote(v_l_4288_, v_prec_4289_, v___x_4306_, v___x_4305_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4307_);
v___x_4309_ = v___x_4301_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v_l_4288_);
v_a_4312_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4298_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4298_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4320_, lean_object* v_prec_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4320_, v_prec_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_prec_4321_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4330_, lean_object* v_stx_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4331_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref(v___x_4335_);
v___x_4337_ = lean_box(0);
v___x_4338_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4336_, v___x_4337_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_n(v_a_4339_, 2);
lean_dec_ref(v___x_4338_);
v___x_4340_ = 0;
v___x_4341_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_a_4339_, v___x_4340_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4348_ == 0)
{
lean_object* v_unused_4349_; 
v_unused_4349_ = lean_ctor_get(v___x_4341_, 0);
lean_dec(v_unused_4349_);
v___x_4343_ = v___x_4341_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_dec(v___x_4341_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v_a_4339_);
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4339_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v_a_4339_);
v_a_4350_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4341_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4341_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
return v___x_4338_;
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
v_a_4358_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4335_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4335_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4366_, lean_object* v_stx_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
uint8_t v_x_409__boxed_4371_; lean_object* v_res_4372_; 
v_x_409__boxed_4371_ = lean_unbox(v_x_4366_);
v_res_4372_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_409__boxed_4371_, v_stx_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4398_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4399_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4397_, v___x_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4405_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4406_ = l_Lean_addBuiltinDocString(v___x_4404_, v___x_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4436_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4437_ = l_Lean_addBuiltinDeclarationRanges(v___x_4435_, v___x_4436_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___redArg(lean_object* v_l_4440_, lean_object* v_prec_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v_options_4446_; lean_object* v_mctx_4447_; uint8_t v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4445_ = lean_st_ref_get(v_a_4442_);
v_options_4446_ = lean_ctor_get(v_a_4443_, 2);
v_mctx_4447_ = lean_ctor_get(v___x_4445_, 0);
lean_inc_ref(v_mctx_4447_);
lean_dec(v___x_4445_);
v___x_4448_ = l_Lean_getPPMVarsLevels(v_options_4446_);
v___x_4449_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4449_, 0, v_mctx_4447_);
v___x_4450_ = l_Lean_Level_quote(v_l_4440_, v_prec_4441_, v___x_4448_, v___x_4449_);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___redArg___boxed(lean_object* v_l_4452_, lean_object* v_prec_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_PrettyPrinter_delabLevel___redArg(v_l_4452_, v_prec_4453_, v_a_4454_, v_a_4455_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec(v_prec_4453_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4458_, lean_object* v_prec_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_PrettyPrinter_delabLevel___redArg(v_l_4458_, v_prec_4459_, v_a_4461_, v_a_4462_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4466_, lean_object* v_prec_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_PrettyPrinter_delabLevel(v_l_4466_, v_prec_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_prec_4467_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___f_4481_; lean_object* v___x_8335__overap_4482_; lean_object* v___x_4483_; 
v___f_4481_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_8335__overap_4482_ = lean_panic_fn_borrowed(v___f_4481_, v_msg_4475_);
lean_inc(v___y_4479_);
lean_inc_ref(v___y_4478_);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
v___x_4483_ = lean_apply_5(v___x_8335__overap_4482_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, lean_box(0));
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4491_, lean_object* v_msg_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4499_, lean_object* v_msg_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4499_, v_msg_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4507_, lean_object* v_opt_4508_){
_start:
{
lean_object* v_name_4509_; lean_object* v_defValue_4510_; lean_object* v_map_4511_; lean_object* v___x_4512_; 
v_name_4509_ = lean_ctor_get(v_opt_4508_, 0);
v_defValue_4510_ = lean_ctor_get(v_opt_4508_, 1);
v_map_4511_ = lean_ctor_get(v_opts_4507_, 0);
v___x_4512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4511_, v_name_4509_);
if (lean_obj_tag(v___x_4512_) == 0)
{
uint8_t v___x_4513_; 
v___x_4513_ = lean_unbox(v_defValue_4510_);
return v___x_4513_;
}
else
{
lean_object* v_val_4514_; 
v_val_4514_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_val_4514_);
lean_dec_ref(v___x_4512_);
if (lean_obj_tag(v_val_4514_) == 1)
{
uint8_t v_v_4515_; 
v_v_4515_ = lean_ctor_get_uint8(v_val_4514_, 0);
lean_dec_ref(v_val_4514_);
return v_v_4515_;
}
else
{
uint8_t v___x_4516_; 
lean_dec(v_val_4514_);
v___x_4516_ = lean_unbox(v_defValue_4510_);
return v___x_4516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4517_, lean_object* v_opt_4518_){
_start:
{
uint8_t v_res_4519_; lean_object* v_r_4520_; 
v_res_4519_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4517_, v_opt_4518_);
lean_dec_ref(v_opt_4518_);
lean_dec_ref(v_opts_4517_);
v_r_4520_ = lean_box(v_res_4519_);
return v_r_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_opts_4521_, lean_object* v_opt_4522_){
_start:
{
lean_object* v_name_4523_; lean_object* v_defValue_4524_; lean_object* v_map_4525_; lean_object* v___x_4526_; 
v_name_4523_ = lean_ctor_get(v_opt_4522_, 0);
v_defValue_4524_ = lean_ctor_get(v_opt_4522_, 1);
v_map_4525_ = lean_ctor_get(v_opts_4521_, 0);
v___x_4526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4525_, v_name_4523_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_inc(v_defValue_4524_);
return v_defValue_4524_;
}
else
{
lean_object* v_val_4527_; 
v_val_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_val_4527_);
lean_dec_ref(v___x_4526_);
if (lean_obj_tag(v_val_4527_) == 3)
{
lean_object* v_v_4528_; 
v_v_4528_ = lean_ctor_get(v_val_4527_, 0);
lean_inc(v_v_4528_);
lean_dec_ref(v_val_4527_);
return v_v_4528_;
}
else
{
lean_dec(v_val_4527_);
lean_inc(v_defValue_4524_);
return v_defValue_4524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_opts_4529_, lean_object* v_opt_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v_opts_4529_, v_opt_4530_);
lean_dec_ref(v_opt_4530_);
lean_dec_ref(v_opts_4529_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(lean_object* v_e_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v___x_4535_; 
v___x_4535_ = l_Lean_Expr_hasMVar(v_e_4532_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_e_4532_);
return v___x_4536_;
}
else
{
lean_object* v___x_4537_; lean_object* v_mctx_4538_; lean_object* v___x_4539_; lean_object* v_fst_4540_; lean_object* v_snd_4541_; lean_object* v___x_4542_; lean_object* v_cache_4543_; lean_object* v_zetaDeltaFVarIds_4544_; lean_object* v_postponed_4545_; lean_object* v_diag_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4555_; 
v___x_4537_ = lean_st_ref_get(v___y_4533_);
v_mctx_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc_ref(v_mctx_4538_);
lean_dec(v___x_4537_);
v___x_4539_ = l_Lean_instantiateMVarsCore(v_mctx_4538_, v_e_4532_);
v_fst_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_fst_4540_);
v_snd_4541_ = lean_ctor_get(v___x_4539_, 1);
lean_inc(v_snd_4541_);
lean_dec_ref(v___x_4539_);
v___x_4542_ = lean_st_ref_take(v___y_4533_);
v_cache_4543_ = lean_ctor_get(v___x_4542_, 1);
v_zetaDeltaFVarIds_4544_ = lean_ctor_get(v___x_4542_, 2);
v_postponed_4545_ = lean_ctor_get(v___x_4542_, 3);
v_diag_4546_ = lean_ctor_get(v___x_4542_, 4);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v___x_4542_, 0);
lean_dec(v_unused_4556_);
v___x_4548_ = v___x_4542_;
v_isShared_4549_ = v_isSharedCheck_4555_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_diag_4546_);
lean_inc(v_postponed_4545_);
lean_inc(v_zetaDeltaFVarIds_4544_);
lean_inc(v_cache_4543_);
lean_dec(v___x_4542_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4555_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v_snd_4541_);
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_snd_4541_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_cache_4543_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_zetaDeltaFVarIds_4544_);
lean_ctor_set(v_reuseFailAlloc_4554_, 3, v_postponed_4545_);
lean_ctor_set(v_reuseFailAlloc_4554_, 4, v_diag_4546_);
v___x_4551_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = lean_st_ref_set(v___y_4533_, v___x_4551_);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v_fst_4540_);
return v___x_4553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg___boxed(lean_object* v_e_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4557_, v___y_4558_);
lean_dec(v___y_4558_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_e_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4561_, v___y_4563_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_e_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(v_e_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4575_, lean_object* v_opt_4576_){
_start:
{
lean_object* v_name_4577_; lean_object* v_map_4578_; lean_object* v___x_4579_; 
v_name_4577_ = lean_ctor_get(v_opt_4576_, 0);
v_map_4578_ = lean_ctor_get(v_opts_4575_, 0);
v___x_4579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4578_, v_name_4577_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_box(0);
return v___x_4580_;
}
else
{
lean_object* v_val_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4591_; 
v_val_4581_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4583_ = v___x_4579_;
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_val_4581_);
lean_dec(v___x_4579_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
if (lean_obj_tag(v_val_4581_) == 1)
{
uint8_t v_v_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v_v_4585_ = lean_ctor_get_uint8(v_val_4581_, 0);
lean_dec_ref(v_val_4581_);
v___x_4586_ = lean_box(v_v_4585_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4586_);
v___x_4588_ = v___x_4583_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
else
{
lean_object* v___x_4590_; 
lean_del_object(v___x_4583_);
lean_dec(v_val_4581_);
v___x_4590_ = lean_box(0);
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4592_, lean_object* v_opt_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4592_, v_opt_4593_);
lean_dec_ref(v_opt_4593_);
lean_dec_ref(v_opts_4592_);
return v_res_4594_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_x_4595_, lean_object* v_x_4596_){
_start:
{
if (lean_obj_tag(v_x_4595_) == 0)
{
if (lean_obj_tag(v_x_4596_) == 0)
{
uint8_t v___x_4597_; 
v___x_4597_ = 1;
return v___x_4597_;
}
else
{
uint8_t v___x_4598_; 
v___x_4598_ = 0;
return v___x_4598_;
}
}
else
{
if (lean_obj_tag(v_x_4596_) == 0)
{
uint8_t v___x_4599_; 
v___x_4599_ = 0;
return v___x_4599_;
}
else
{
lean_object* v_val_4600_; uint8_t v___x_4601_; 
v_val_4600_ = lean_ctor_get(v_x_4595_, 0);
v___x_4601_ = lean_unbox(v_val_4600_);
if (v___x_4601_ == 0)
{
lean_object* v_val_4602_; uint8_t v___x_4603_; 
v_val_4602_ = lean_ctor_get(v_x_4596_, 0);
v___x_4603_ = lean_unbox(v_val_4602_);
if (v___x_4603_ == 0)
{
uint8_t v___x_4604_; 
v___x_4604_ = 1;
return v___x_4604_;
}
else
{
uint8_t v___x_4605_; 
v___x_4605_ = lean_unbox(v_val_4600_);
return v___x_4605_;
}
}
else
{
lean_object* v_val_4606_; uint8_t v___x_4607_; 
v_val_4606_ = lean_ctor_get(v_x_4596_, 0);
v___x_4607_ = lean_unbox(v_val_4606_);
return v___x_4607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_x_4608_, lean_object* v_x_4609_){
_start:
{
uint8_t v_res_4610_; lean_object* v_r_4611_; 
v_res_4610_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v_x_4608_, v_x_4609_);
lean_dec(v_x_4609_);
lean_dec(v_x_4608_);
v_r_4611_ = lean_box(v_res_4610_);
return v_r_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object* v_o_4612_, lean_object* v_k_4613_, uint8_t v_v_4614_){
_start:
{
lean_object* v_map_4615_; uint8_t v_hasTrace_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4630_; 
v_map_4615_ = lean_ctor_get(v_o_4612_, 0);
v_hasTrace_4616_ = lean_ctor_get_uint8(v_o_4612_, sizeof(void*)*1);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_o_4612_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4618_ = v_o_4612_;
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_map_4615_);
lean_dec(v_o_4612_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4620_, 0, v_v_4614_);
lean_inc(v_k_4613_);
v___x_4621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4613_, v___x_4620_, v_map_4615_);
if (v_hasTrace_4616_ == 0)
{
lean_object* v___x_4622_; uint8_t v___x_4623_; lean_object* v___x_4625_; 
v___x_4622_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_4623_ = l_Lean_Name_isPrefixOf(v___x_4622_, v_k_4613_);
lean_dec(v_k_4613_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4621_);
v___x_4625_ = v___x_4618_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4621_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*1, v___x_4623_);
return v___x_4625_;
}
}
else
{
lean_object* v___x_4628_; 
lean_dec(v_k_4613_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4621_);
v___x_4628_ = v___x_4618_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4621_);
lean_ctor_set_uint8(v_reuseFailAlloc_4629_, sizeof(void*)*1, v_hasTrace_4616_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object* v_o_4631_, lean_object* v_k_4632_, lean_object* v_v_4633_){
_start:
{
uint8_t v_v_boxed_4634_; lean_object* v_res_4635_; 
v_v_boxed_4634_ = lean_unbox(v_v_4633_);
v_res_4635_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_o_4631_, v_k_4632_, v_v_boxed_4634_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4636_, lean_object* v_opt_4637_, uint8_t v_val_4638_){
_start:
{
lean_object* v_name_4639_; lean_object* v___x_4640_; 
v_name_4639_ = lean_ctor_get(v_opt_4637_, 0);
lean_inc(v_name_4639_);
lean_dec_ref(v_opt_4637_);
v___x_4640_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_opts_4636_, v_name_4639_, v_val_4638_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4641_, lean_object* v_opt_4642_, lean_object* v_val_4643_){
_start:
{
uint8_t v_val_boxed_4644_; lean_object* v_res_4645_; 
v_val_boxed_4644_ = lean_unbox(v_val_4643_);
v_res_4645_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4641_, v_opt_4642_, v_val_boxed_4644_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object* v_cls_4646_, lean_object* v_msg_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_ref_4653_; lean_object* v___x_4654_; lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4699_; 
v_ref_4653_ = lean_ctor_get(v___y_4650_, 5);
v___x_4654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4657_ = v___x_4654_;
v_isShared_4658_ = v_isSharedCheck_4699_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4654_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4699_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4659_; lean_object* v_traceState_4660_; lean_object* v_env_4661_; lean_object* v_nextMacroScope_4662_; lean_object* v_ngen_4663_; lean_object* v_auxDeclNGen_4664_; lean_object* v_cache_4665_; lean_object* v_messages_4666_; lean_object* v_infoState_4667_; lean_object* v_snapshotTasks_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4698_; 
v___x_4659_ = lean_st_ref_take(v___y_4651_);
v_traceState_4660_ = lean_ctor_get(v___x_4659_, 4);
v_env_4661_ = lean_ctor_get(v___x_4659_, 0);
v_nextMacroScope_4662_ = lean_ctor_get(v___x_4659_, 1);
v_ngen_4663_ = lean_ctor_get(v___x_4659_, 2);
v_auxDeclNGen_4664_ = lean_ctor_get(v___x_4659_, 3);
v_cache_4665_ = lean_ctor_get(v___x_4659_, 5);
v_messages_4666_ = lean_ctor_get(v___x_4659_, 6);
v_infoState_4667_ = lean_ctor_get(v___x_4659_, 7);
v_snapshotTasks_4668_ = lean_ctor_get(v___x_4659_, 8);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4670_ = v___x_4659_;
v_isShared_4671_ = v_isSharedCheck_4698_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_snapshotTasks_4668_);
lean_inc(v_infoState_4667_);
lean_inc(v_messages_4666_);
lean_inc(v_cache_4665_);
lean_inc(v_traceState_4660_);
lean_inc(v_auxDeclNGen_4664_);
lean_inc(v_ngen_4663_);
lean_inc(v_nextMacroScope_4662_);
lean_inc(v_env_4661_);
lean_dec(v___x_4659_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4698_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
uint64_t v_tid_4672_; lean_object* v_traces_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4697_; 
v_tid_4672_ = lean_ctor_get_uint64(v_traceState_4660_, sizeof(void*)*1);
v_traces_4673_ = lean_ctor_get(v_traceState_4660_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v_traceState_4660_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4675_ = v_traceState_4660_;
v_isShared_4676_ = v_isSharedCheck_4697_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_traces_4673_);
lean_dec(v_traceState_4660_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4697_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; double v___x_4678_; uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__0);
v___x_4679_ = 0;
v___x_4680_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__1));
v___x_4681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4681_, 0, v_cls_4646_);
lean_ctor_set(v___x_4681_, 1, v___x_4677_);
lean_ctor_set(v___x_4681_, 2, v___x_4680_);
lean_ctor_set_float(v___x_4681_, sizeof(void*)*3, v___x_4678_);
lean_ctor_set_float(v___x_4681_, sizeof(void*)*3 + 8, v___x_4678_);
lean_ctor_set_uint8(v___x_4681_, sizeof(void*)*3 + 16, v___x_4679_);
v___x_4682_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___closed__2));
v___x_4683_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4681_);
lean_ctor_set(v___x_4683_, 1, v_a_4655_);
lean_ctor_set(v___x_4683_, 2, v___x_4682_);
lean_inc(v_ref_4653_);
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v_ref_4653_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l_Lean_PersistentArray_push___redArg(v_traces_4673_, v___x_4684_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4685_);
v___x_4687_ = v___x_4675_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4685_);
lean_ctor_set_uint64(v_reuseFailAlloc_4696_, sizeof(void*)*1, v_tid_4672_);
v___x_4687_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4689_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 4, v___x_4687_);
v___x_4689_ = v___x_4670_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_env_4661_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_nextMacroScope_4662_);
lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_ngen_4663_);
lean_ctor_set(v_reuseFailAlloc_4695_, 3, v_auxDeclNGen_4664_);
lean_ctor_set(v_reuseFailAlloc_4695_, 4, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4695_, 5, v_cache_4665_);
lean_ctor_set(v_reuseFailAlloc_4695_, 6, v_messages_4666_);
lean_ctor_set(v_reuseFailAlloc_4695_, 7, v_infoState_4667_);
lean_ctor_set(v_reuseFailAlloc_4695_, 8, v_snapshotTasks_4668_);
v___x_4689_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; 
v___x_4690_ = lean_st_ref_set(v___y_4651_, v___x_4689_);
v___x_4691_ = lean_box(0);
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 0, v___x_4691_);
v___x_4693_ = v___x_4657_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object* v_cls_4700_, lean_object* v_msg_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v_cls_4700_, v_msg_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
return v_res_4707_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4711_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4712_ = lean_unsigned_to_nat(18u);
v___x_4713_ = lean_unsigned_to_nat(519u);
v___x_4714_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4715_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4716_ = l_mkPanicMessageWithDecl(v___x_4715_, v___x_4714_, v___x_4713_, v___x_4712_, v___x_4711_);
return v___x_4716_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4717_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4718_ = lean_unsigned_to_nat(2u);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4718_);
lean_ctor_set(v___x_4719_, 1, v___x_4717_);
return v___x_4719_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4720_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4721_ = lean_box(1);
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
lean_ctor_set(v___x_4723_, 1, v___x_4721_);
lean_ctor_set(v___x_4723_, 2, v___x_4720_);
return v___x_4723_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4729_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4730_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14));
v___x_4731_ = l_Lean_Name_append(v___x_4730_, v___x_4729_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4732_, lean_object* v_optionsPerPos_4733_, lean_object* v_delab_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_fst_4741_; lean_object* v_snd_4742_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; uint8_t v___y_4753_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v_optionsPerPos_4775_; lean_object* v___y_4776_; lean_object* v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4811_; lean_object* v_e_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4830_; lean_object* v_e_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___x_4847_; 
v___x_4847_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4732_, v_a_4737_, v_a_4738_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4975_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4975_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4975_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___y_4853_; uint8_t v___y_4854_; uint8_t v___y_4855_; lean_object* v___y_4856_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v___y_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; uint8_t v___y_4882_; uint8_t v___y_4883_; lean_object* v___y_4884_; lean_object* v___y_4885_; uint8_t v___y_4886_; lean_object* v_opts_4908_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___y_4924_; lean_object* v___y_4925_; uint8_t v___y_4926_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; uint8_t v___y_4937_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; lean_object* v_options_4950_; lean_object* v___y_4951_; lean_object* v_options_4957_; uint8_t v_hasTrace_4958_; 
v_options_4957_ = lean_ctor_get(v_a_4737_, 2);
v_hasTrace_4958_ = lean_ctor_get_uint8(v_options_4957_, sizeof(void*)*1);
if (v_hasTrace_4958_ == 0)
{
v___y_4947_ = v_a_4735_;
v___y_4948_ = v_a_4736_;
v___y_4949_ = v_a_4737_;
v_options_4950_ = v_options_4957_;
v___y_4951_ = v_a_4738_;
goto v___jp_4946_;
}
else
{
lean_object* v_inheritedTraceOptions_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
v_inheritedTraceOptions_4959_ = lean_ctor_get(v_a_4737_, 13);
v___x_4960_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4961_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_4962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4959_, v_options_4957_, v___x_4961_);
if (v___x_4962_ == 0)
{
v___y_4947_ = v_a_4735_;
v___y_4948_ = v_a_4736_;
v___y_4949_ = v_a_4737_;
v_options_4950_ = v_options_4957_;
v___y_4951_ = v_a_4738_;
goto v___jp_4946_;
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4963_ = lean_expr_dbg_to_string(v_a_4848_);
v___x_4964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
v___x_4965_ = l_Lean_MessageData_ofFormat(v___x_4964_);
v___x_4966_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v___x_4960_, v___x_4965_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_dec_ref(v___x_4966_);
v___y_4947_ = v_a_4735_;
v___y_4948_ = v_a_4736_;
v___y_4949_ = v_a_4737_;
v_options_4950_ = v_options_4957_;
v___y_4951_ = v_a_4738_;
goto v___jp_4946_;
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_del_object(v___x_4850_);
lean_dec(v_a_4848_);
lean_dec_ref(v_delab_4734_);
lean_dec(v_optionsPerPos_4733_);
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4966_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4966_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
v___jp_4852_:
{
lean_object* v_fileName_4860_; lean_object* v_fileMap_4861_; lean_object* v_currRecDepth_4862_; lean_object* v_ref_4863_; lean_object* v_currNamespace_4864_; lean_object* v_openDecls_4865_; lean_object* v_initHeartbeats_4866_; lean_object* v_maxHeartbeats_4867_; lean_object* v_quotContext_4868_; lean_object* v_currMacroScope_4869_; lean_object* v_cancelTk_x3f_4870_; uint8_t v_suppressElabErrors_4871_; lean_object* v_inheritedTraceOptions_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v_fileName_4860_ = lean_ctor_get(v___y_4858_, 0);
v_fileMap_4861_ = lean_ctor_get(v___y_4858_, 1);
v_currRecDepth_4862_ = lean_ctor_get(v___y_4858_, 3);
v_ref_4863_ = lean_ctor_get(v___y_4858_, 5);
v_currNamespace_4864_ = lean_ctor_get(v___y_4858_, 6);
v_openDecls_4865_ = lean_ctor_get(v___y_4858_, 7);
v_initHeartbeats_4866_ = lean_ctor_get(v___y_4858_, 8);
v_maxHeartbeats_4867_ = lean_ctor_get(v___y_4858_, 9);
v_quotContext_4868_ = lean_ctor_get(v___y_4858_, 10);
v_currMacroScope_4869_ = lean_ctor_get(v___y_4858_, 11);
v_cancelTk_x3f_4870_ = lean_ctor_get(v___y_4858_, 12);
v_suppressElabErrors_4871_ = lean_ctor_get_uint8(v___y_4858_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4872_ = lean_ctor_get(v___y_4858_, 13);
v___x_4873_ = l_Lean_maxRecDepth;
v___x_4874_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v___y_4857_, v___x_4873_);
lean_inc_ref(v_inheritedTraceOptions_4872_);
lean_inc(v_cancelTk_x3f_4870_);
lean_inc(v_currMacroScope_4869_);
lean_inc(v_quotContext_4868_);
lean_inc(v_maxHeartbeats_4867_);
lean_inc(v_initHeartbeats_4866_);
lean_inc(v_openDecls_4865_);
lean_inc(v_currNamespace_4864_);
lean_inc(v_ref_4863_);
lean_inc(v_currRecDepth_4862_);
lean_inc_ref(v___y_4857_);
lean_inc_ref(v_fileMap_4861_);
lean_inc_ref(v_fileName_4860_);
v___x_4875_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4875_, 0, v_fileName_4860_);
lean_ctor_set(v___x_4875_, 1, v_fileMap_4861_);
lean_ctor_set(v___x_4875_, 2, v___y_4857_);
lean_ctor_set(v___x_4875_, 3, v_currRecDepth_4862_);
lean_ctor_set(v___x_4875_, 4, v___x_4874_);
lean_ctor_set(v___x_4875_, 5, v_ref_4863_);
lean_ctor_set(v___x_4875_, 6, v_currNamespace_4864_);
lean_ctor_set(v___x_4875_, 7, v_openDecls_4865_);
lean_ctor_set(v___x_4875_, 8, v_initHeartbeats_4866_);
lean_ctor_set(v___x_4875_, 9, v_maxHeartbeats_4867_);
lean_ctor_set(v___x_4875_, 10, v_quotContext_4868_);
lean_ctor_set(v___x_4875_, 11, v_currMacroScope_4869_);
lean_ctor_set(v___x_4875_, 12, v_cancelTk_x3f_4870_);
lean_ctor_set(v___x_4875_, 13, v_inheritedTraceOptions_4872_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*14, v___y_4854_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*14 + 1, v_suppressElabErrors_4871_);
if (v___y_4855_ == 0)
{
v___y_4830_ = v___y_4857_;
v_e_4831_ = v_a_4848_;
v___y_4832_ = v___y_4853_;
v___y_4833_ = v___y_4856_;
v___y_4834_ = v___x_4875_;
v___y_4835_ = v___y_4859_;
goto v___jp_4829_;
}
else
{
lean_object* v___x_4876_; lean_object* v_a_4877_; 
v___x_4876_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_a_4848_, v___y_4856_);
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v___y_4830_ = v___y_4857_;
v_e_4831_ = v_a_4877_;
v___y_4832_ = v___y_4853_;
v___y_4833_ = v___y_4856_;
v___y_4834_ = v___x_4875_;
v___y_4835_ = v___y_4859_;
goto v___jp_4829_;
}
}
v___jp_4878_:
{
if (v___y_4886_ == 0)
{
lean_object* v___x_4887_; lean_object* v_env_4888_; lean_object* v_nextMacroScope_4889_; lean_object* v_ngen_4890_; lean_object* v_auxDeclNGen_4891_; lean_object* v_traceState_4892_; lean_object* v_messages_4893_; lean_object* v_infoState_4894_; lean_object* v_snapshotTasks_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4905_; 
v___x_4887_ = lean_st_ref_take(v___y_4881_);
v_env_4888_ = lean_ctor_get(v___x_4887_, 0);
v_nextMacroScope_4889_ = lean_ctor_get(v___x_4887_, 1);
v_ngen_4890_ = lean_ctor_get(v___x_4887_, 2);
v_auxDeclNGen_4891_ = lean_ctor_get(v___x_4887_, 3);
v_traceState_4892_ = lean_ctor_get(v___x_4887_, 4);
v_messages_4893_ = lean_ctor_get(v___x_4887_, 6);
v_infoState_4894_ = lean_ctor_get(v___x_4887_, 7);
v_snapshotTasks_4895_ = lean_ctor_get(v___x_4887_, 8);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v___x_4887_, 5);
lean_dec(v_unused_4906_);
v___x_4897_ = v___x_4887_;
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_snapshotTasks_4895_);
lean_inc(v_infoState_4894_);
lean_inc(v_messages_4893_);
lean_inc(v_traceState_4892_);
lean_inc(v_auxDeclNGen_4891_);
lean_inc(v_ngen_4890_);
lean_inc(v_nextMacroScope_4889_);
lean_inc(v_env_4888_);
lean_dec(v___x_4887_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4899_ = l_Lean_Kernel_enableDiag(v_env_4888_, v___y_4882_);
v___x_4900_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 5, v___x_4900_);
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4902_ = v___x_4897_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_nextMacroScope_4889_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_ngen_4890_);
lean_ctor_set(v_reuseFailAlloc_4904_, 3, v_auxDeclNGen_4891_);
lean_ctor_set(v_reuseFailAlloc_4904_, 4, v_traceState_4892_);
lean_ctor_set(v_reuseFailAlloc_4904_, 5, v___x_4900_);
lean_ctor_set(v_reuseFailAlloc_4904_, 6, v_messages_4893_);
lean_ctor_set(v_reuseFailAlloc_4904_, 7, v_infoState_4894_);
lean_ctor_set(v_reuseFailAlloc_4904_, 8, v_snapshotTasks_4895_);
v___x_4902_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
lean_object* v___x_4903_; 
v___x_4903_ = lean_st_ref_set(v___y_4881_, v___x_4902_);
v___y_4853_ = v___y_4879_;
v___y_4854_ = v___y_4882_;
v___y_4855_ = v___y_4883_;
v___y_4856_ = v___y_4884_;
v___y_4857_ = v___y_4885_;
v___y_4858_ = v___y_4880_;
v___y_4859_ = v___y_4881_;
goto v___jp_4852_;
}
}
}
else
{
v___y_4853_ = v___y_4879_;
v___y_4854_ = v___y_4882_;
v___y_4855_ = v___y_4883_;
v___y_4856_ = v___y_4884_;
v___y_4857_ = v___y_4885_;
v___y_4858_ = v___y_4880_;
v___y_4859_ = v___y_4881_;
goto v___jp_4852_;
}
}
v___jp_4907_:
{
lean_object* v___x_4913_; lean_object* v_env_4914_; uint8_t v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; uint8_t v___x_4918_; 
v___x_4913_ = lean_st_ref_get(v___y_4912_);
v_env_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc_ref(v_env_4914_);
lean_dec(v___x_4913_);
v___x_4915_ = l_Lean_getPPInstantiateMVars(v_opts_4908_);
v___x_4916_ = l_Lean_diagnostics;
v___x_4917_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4908_, v___x_4916_);
v___x_4918_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4914_);
lean_dec_ref(v_env_4914_);
if (v___x_4918_ == 0)
{
if (v___x_4917_ == 0)
{
v___y_4853_ = v___y_4909_;
v___y_4854_ = v___x_4917_;
v___y_4855_ = v___x_4915_;
v___y_4856_ = v___y_4910_;
v___y_4857_ = v_opts_4908_;
v___y_4858_ = v___y_4911_;
v___y_4859_ = v___y_4912_;
goto v___jp_4852_;
}
else
{
v___y_4879_ = v___y_4909_;
v___y_4880_ = v___y_4911_;
v___y_4881_ = v___y_4912_;
v___y_4882_ = v___x_4917_;
v___y_4883_ = v___x_4915_;
v___y_4884_ = v___y_4910_;
v___y_4885_ = v_opts_4908_;
v___y_4886_ = v___x_4918_;
goto v___jp_4878_;
}
}
else
{
v___y_4879_ = v___y_4909_;
v___y_4880_ = v___y_4911_;
v___y_4881_ = v___y_4912_;
v___y_4882_ = v___x_4917_;
v___y_4883_ = v___x_4915_;
v___y_4884_ = v___y_4910_;
v___y_4885_ = v_opts_4908_;
v___y_4886_ = v___x_4917_;
goto v___jp_4878_;
}
}
v___jp_4919_:
{
if (v___y_4926_ == 0)
{
lean_dec_ref(v___y_4921_);
lean_del_object(v___x_4850_);
lean_inc_ref(v___y_4923_);
v_opts_4908_ = v___y_4923_;
v___y_4909_ = v___y_4922_;
v___y_4910_ = v___y_4925_;
v___y_4911_ = v___y_4920_;
v___y_4912_ = v___y_4924_;
goto v___jp_4907_;
}
else
{
lean_object* v___x_4928_; 
lean_dec(v_a_4848_);
lean_dec_ref(v_delab_4734_);
lean_dec(v_optionsPerPos_4733_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set_tag(v___x_4850_, 1);
lean_ctor_set(v___x_4850_, 0, v___y_4921_);
v___x_4928_ = v___x_4850_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___y_4921_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
v___jp_4930_:
{
if (v___y_4937_ == 0)
{
lean_del_object(v___x_4850_);
lean_inc_ref(v___y_4934_);
v_opts_4908_ = v___y_4934_;
v___y_4909_ = v___y_4933_;
v___y_4910_ = v___y_4936_;
v___y_4911_ = v___y_4932_;
v___y_4912_ = v___y_4935_;
goto v___jp_4907_;
}
else
{
lean_object* v___x_4938_; 
lean_inc(v_a_4848_);
v___x_4938_ = l_Lean_Meta_isProof(v_a_4848_, v___y_4933_, v___y_4936_, v___y_4932_, v___y_4935_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; uint8_t v___x_4940_; 
lean_del_object(v___x_4850_);
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref(v___x_4938_);
v___x_4940_ = lean_unbox(v_a_4939_);
if (v___x_4940_ == 0)
{
lean_dec(v_a_4939_);
lean_inc_ref(v___y_4934_);
v_opts_4908_ = v___y_4934_;
v___y_4909_ = v___y_4933_;
v___y_4910_ = v___y_4936_;
v___y_4911_ = v___y_4932_;
v___y_4912_ = v___y_4935_;
goto v___jp_4907_;
}
else
{
uint8_t v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = lean_unbox(v_a_4939_);
lean_dec(v_a_4939_);
lean_inc_ref(v___y_4931_);
lean_inc_ref(v___y_4934_);
v___x_4942_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v___y_4934_, v___y_4931_, v___x_4941_);
v_opts_4908_ = v___x_4942_;
v___y_4909_ = v___y_4933_;
v___y_4910_ = v___y_4936_;
v___y_4911_ = v___y_4932_;
v___y_4912_ = v___y_4935_;
goto v___jp_4907_;
}
}
else
{
lean_object* v_a_4943_; uint8_t v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4943_);
lean_dec_ref(v___x_4938_);
v___x_4944_ = l_Lean_Exception_isInterrupt(v_a_4943_);
if (v___x_4944_ == 0)
{
uint8_t v___x_4945_; 
lean_inc(v_a_4943_);
v___x_4945_ = l_Lean_Exception_isRuntime(v_a_4943_);
v___y_4920_ = v___y_4932_;
v___y_4921_ = v_a_4943_;
v___y_4922_ = v___y_4933_;
v___y_4923_ = v___y_4934_;
v___y_4924_ = v___y_4935_;
v___y_4925_ = v___y_4936_;
v___y_4926_ = v___x_4945_;
goto v___jp_4919_;
}
else
{
v___y_4920_ = v___y_4932_;
v___y_4921_ = v_a_4943_;
v___y_4922_ = v___y_4933_;
v___y_4923_ = v___y_4934_;
v___y_4924_ = v___y_4935_;
v___y_4925_ = v___y_4936_;
v___y_4926_ = v___x_4944_;
goto v___jp_4919_;
}
}
}
}
v___jp_4946_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; uint8_t v___x_4955_; 
v___x_4952_ = l_Lean_pp_proofs;
v___x_4953_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_options_4950_, v___x_4952_);
v___x_4954_ = lean_box(0);
v___x_4955_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_4953_, v___x_4954_);
lean_dec(v___x_4953_);
if (v___x_4955_ == 0)
{
v___y_4931_ = v___x_4952_;
v___y_4932_ = v___y_4949_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v_options_4950_;
v___y_4935_ = v___y_4951_;
v___y_4936_ = v___y_4948_;
v___y_4937_ = v___x_4955_;
goto v___jp_4930_;
}
else
{
uint8_t v___x_4956_; 
v___x_4956_ = l_Lean_Expr_isConst(v_a_4848_);
if (v___x_4956_ == 0)
{
v___y_4931_ = v___x_4952_;
v___y_4932_ = v___y_4949_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v_options_4950_;
v___y_4935_ = v___y_4951_;
v___y_4936_ = v___y_4948_;
v___y_4937_ = v___x_4955_;
goto v___jp_4930_;
}
else
{
lean_del_object(v___x_4850_);
lean_inc_ref(v_options_4950_);
v_opts_4908_ = v_options_4950_;
v___y_4909_ = v___y_4947_;
v___y_4910_ = v___y_4948_;
v___y_4911_ = v___y_4949_;
v___y_4912_ = v___y_4951_;
goto v___jp_4907_;
}
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v_delab_4734_);
lean_dec(v_optionsPerPos_4733_);
v_a_4976_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4847_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4847_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
v___jp_4740_:
{
lean_object* v_infos_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v_infos_4743_ = lean_ctor_get(v_snd_4742_, 1);
lean_inc(v_infos_4743_);
lean_dec_ref(v_snd_4742_);
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v_fst_4741_);
lean_ctor_set(v___x_4744_, 1, v_infos_4743_);
v___x_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4744_);
return v___x_4745_;
}
v___jp_4746_:
{
if (v___y_4753_ == 0)
{
if (lean_obj_tag(v___y_4752_) == 0)
{
lean_object* v___x_4754_; 
lean_dec_ref(v___y_4750_);
v___x_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___y_4752_);
return v___x_4754_;
}
else
{
lean_object* v_id_4755_; uint8_t v___x_4756_; 
v_id_4755_ = lean_ctor_get(v___y_4752_, 0);
v___x_4756_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4747_, v_id_4755_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
lean_dec_ref(v___y_4750_);
v___x_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___y_4752_);
return v___x_4757_;
}
else
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec_ref(v___y_4752_);
v___x_4758_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4759_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4758_, v___y_4749_, v___y_4748_, v___y_4750_, v___y_4751_);
lean_dec_ref(v___y_4750_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v_fst_4761_; lean_object* v_snd_4762_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref(v___x_4759_);
v_fst_4761_ = lean_ctor_get(v_a_4760_, 0);
lean_inc(v_fst_4761_);
v_snd_4762_ = lean_ctor_get(v_a_4760_, 1);
lean_inc(v_snd_4762_);
lean_dec(v_a_4760_);
v_fst_4741_ = v_fst_4761_;
v_snd_4742_ = v_snd_4762_;
goto v___jp_4740_;
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v_a_4763_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4759_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4759_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
else
{
lean_object* v___x_4771_; 
lean_dec_ref(v___y_4750_);
v___x_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___y_4752_);
return v___x_4771_;
}
}
v___jp_4772_:
{
lean_object* v_fileName_4780_; lean_object* v_fileMap_4781_; lean_object* v_options_4782_; lean_object* v_currRecDepth_4783_; lean_object* v_maxRecDepth_4784_; lean_object* v_currNamespace_4785_; lean_object* v_openDecls_4786_; lean_object* v_initHeartbeats_4787_; lean_object* v_maxHeartbeats_4788_; lean_object* v_quotContext_4789_; lean_object* v_currMacroScope_4790_; uint8_t v_diag_4791_; lean_object* v_cancelTk_x3f_4792_; uint8_t v_suppressElabErrors_4793_; lean_object* v_inheritedTraceOptions_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_fileName_4780_ = lean_ctor_get(v___y_4778_, 0);
v_fileMap_4781_ = lean_ctor_get(v___y_4778_, 1);
v_options_4782_ = lean_ctor_get(v___y_4778_, 2);
v_currRecDepth_4783_ = lean_ctor_get(v___y_4778_, 3);
v_maxRecDepth_4784_ = lean_ctor_get(v___y_4778_, 4);
v_currNamespace_4785_ = lean_ctor_get(v___y_4778_, 6);
v_openDecls_4786_ = lean_ctor_get(v___y_4778_, 7);
v_initHeartbeats_4787_ = lean_ctor_get(v___y_4778_, 8);
v_maxHeartbeats_4788_ = lean_ctor_get(v___y_4778_, 9);
v_quotContext_4789_ = lean_ctor_get(v___y_4778_, 10);
v_currMacroScope_4790_ = lean_ctor_get(v___y_4778_, 11);
v_diag_4791_ = lean_ctor_get_uint8(v___y_4778_, sizeof(void*)*14);
v_cancelTk_x3f_4792_ = lean_ctor_get(v___y_4778_, 12);
v_suppressElabErrors_4793_ = lean_ctor_get_uint8(v___y_4778_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4794_ = lean_ctor_get(v___y_4778_, 13);
v___x_4795_ = l_Lean_Options_getInPattern(v___y_4774_);
lean_dec_ref(v___y_4774_);
v___x_4796_ = l_Lean_SubExpr_mkRoot(v___y_4773_);
v___x_4797_ = lean_unsigned_to_nat(0u);
lean_inc_n(v_openDecls_4786_, 2);
lean_inc_n(v_currNamespace_4785_, 2);
v___x_4798_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4798_, 0, v_optionsPerPos_4775_);
lean_ctor_set(v___x_4798_, 1, v_currNamespace_4785_);
lean_ctor_set(v___x_4798_, 2, v_openDecls_4786_);
lean_ctor_set(v___x_4798_, 3, v___x_4796_);
lean_ctor_set(v___x_4798_, 4, v___x_4797_);
lean_ctor_set_uint8(v___x_4798_, sizeof(void*)*5, v___x_4795_);
v___x_4799_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4800_ = lean_st_mk_ref(v___x_4799_);
v___x_4801_ = lean_box(0);
lean_inc_ref(v_inheritedTraceOptions_4794_);
lean_inc(v_cancelTk_x3f_4792_);
lean_inc(v_currMacroScope_4790_);
lean_inc(v_quotContext_4789_);
lean_inc(v_maxHeartbeats_4788_);
lean_inc(v_initHeartbeats_4787_);
lean_inc(v_maxRecDepth_4784_);
lean_inc(v_currRecDepth_4783_);
lean_inc_ref(v_options_4782_);
lean_inc_ref(v_fileMap_4781_);
lean_inc_ref(v_fileName_4780_);
v___x_4802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4802_, 0, v_fileName_4780_);
lean_ctor_set(v___x_4802_, 1, v_fileMap_4781_);
lean_ctor_set(v___x_4802_, 2, v_options_4782_);
lean_ctor_set(v___x_4802_, 3, v_currRecDepth_4783_);
lean_ctor_set(v___x_4802_, 4, v_maxRecDepth_4784_);
lean_ctor_set(v___x_4802_, 5, v___x_4801_);
lean_ctor_set(v___x_4802_, 6, v_currNamespace_4785_);
lean_ctor_set(v___x_4802_, 7, v_openDecls_4786_);
lean_ctor_set(v___x_4802_, 8, v_initHeartbeats_4787_);
lean_ctor_set(v___x_4802_, 9, v_maxHeartbeats_4788_);
lean_ctor_set(v___x_4802_, 10, v_quotContext_4789_);
lean_ctor_set(v___x_4802_, 11, v_currMacroScope_4790_);
lean_ctor_set(v___x_4802_, 12, v_cancelTk_x3f_4792_);
lean_ctor_set(v___x_4802_, 13, v_inheritedTraceOptions_4794_);
lean_ctor_set_uint8(v___x_4802_, sizeof(void*)*14, v_diag_4791_);
lean_ctor_set_uint8(v___x_4802_, sizeof(void*)*14 + 1, v_suppressElabErrors_4793_);
lean_inc(v___y_4779_);
lean_inc(v___y_4777_);
lean_inc_ref(v___y_4776_);
lean_inc(v___x_4800_);
v___x_4803_ = lean_apply_7(v_delab_4734_, v___x_4798_, v___x_4800_, v___y_4776_, v___y_4777_, v___x_4802_, v___y_4779_, lean_box(0));
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; 
lean_dec_ref(v___y_4778_);
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v___x_4803_);
v___x_4805_ = lean_st_ref_get(v___x_4800_);
lean_dec(v___x_4800_);
v_fst_4741_ = v_a_4804_;
v_snd_4742_ = v___x_4805_;
goto v___jp_4740_;
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
lean_dec(v___x_4800_);
v_a_4806_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4806_);
lean_dec_ref(v___x_4803_);
v___x_4807_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4808_ = l_Lean_Exception_isInterrupt(v_a_4806_);
if (v___x_4808_ == 0)
{
uint8_t v___x_4809_; 
lean_inc(v_a_4806_);
v___x_4809_ = l_Lean_Exception_isRuntime(v_a_4806_);
v___y_4747_ = v___x_4807_;
v___y_4748_ = v___y_4777_;
v___y_4749_ = v___y_4776_;
v___y_4750_ = v___y_4778_;
v___y_4751_ = v___y_4779_;
v___y_4752_ = v_a_4806_;
v___y_4753_ = v___x_4809_;
goto v___jp_4746_;
}
else
{
v___y_4747_ = v___x_4807_;
v___y_4748_ = v___y_4777_;
v___y_4749_ = v___y_4776_;
v___y_4750_ = v___y_4778_;
v___y_4751_ = v___y_4779_;
v___y_4752_ = v_a_4806_;
v___y_4753_ = v___x_4808_;
goto v___jp_4746_;
}
}
}
v___jp_4810_:
{
uint8_t v___x_4817_; 
v___x_4817_ = l_Lean_getPPAll(v___y_4811_);
if (v___x_4817_ == 0)
{
uint8_t v___x_4818_; 
v___x_4818_ = l_Lean_getPPAnalyze(v___y_4811_);
if (v___x_4818_ == 0)
{
v___y_4773_ = v_e_4812_;
v___y_4774_ = v___y_4811_;
v_optionsPerPos_4775_ = v_optionsPerPos_4733_;
v___y_4776_ = v___y_4813_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v___y_4815_;
v___y_4779_ = v___y_4816_;
goto v___jp_4772_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4733_) == 0)
{
v___y_4773_ = v_e_4812_;
v___y_4774_ = v___y_4811_;
v_optionsPerPos_4775_ = v_optionsPerPos_4733_;
v___y_4776_ = v___y_4813_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v___y_4815_;
v___y_4779_ = v___y_4816_;
goto v___jp_4772_;
}
else
{
lean_object* v___x_4819_; 
lean_inc_ref(v_e_4812_);
v___x_4819_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
lean_inc(v_a_4820_);
lean_dec_ref(v___x_4819_);
v___y_4773_ = v_e_4812_;
v___y_4774_ = v___y_4811_;
v_optionsPerPos_4775_ = v_a_4820_;
v___y_4776_ = v___y_4813_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v___y_4815_;
v___y_4779_ = v___y_4816_;
goto v___jp_4772_;
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec_ref(v___y_4815_);
lean_dec_ref(v_e_4812_);
lean_dec_ref(v___y_4811_);
lean_dec_ref(v_delab_4734_);
v_a_4821_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4819_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4819_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
}
else
{
v___y_4773_ = v_e_4812_;
v___y_4774_ = v___y_4811_;
v_optionsPerPos_4775_ = v_optionsPerPos_4733_;
v___y_4776_ = v___y_4813_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v___y_4815_;
v___y_4779_ = v___y_4816_;
goto v___jp_4772_;
}
}
v___jp_4829_:
{
uint8_t v___x_4836_; 
v___x_4836_ = l_Lean_getPPBeta(v___y_4830_);
if (v___x_4836_ == 0)
{
v___y_4811_ = v___y_4830_;
v_e_4812_ = v_e_4831_;
v___y_4813_ = v___y_4832_;
v___y_4814_ = v___y_4833_;
v___y_4815_ = v___y_4834_;
v___y_4816_ = v___y_4835_;
goto v___jp_4810_;
}
else
{
lean_object* v___x_4837_; 
v___x_4837_ = l_Lean_Core_betaReduce(v_e_4831_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4837_) == 0)
{
lean_object* v_a_4838_; 
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc(v_a_4838_);
lean_dec_ref(v___x_4837_);
v___y_4811_ = v___y_4830_;
v_e_4812_ = v_a_4838_;
v___y_4813_ = v___y_4832_;
v___y_4814_ = v___y_4833_;
v___y_4815_ = v___y_4834_;
v___y_4816_ = v___y_4835_;
goto v___jp_4810_;
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec_ref(v___y_4834_);
lean_dec_ref(v___y_4830_);
lean_dec_ref(v_delab_4734_);
lean_dec(v_optionsPerPos_4733_);
v_a_4839_ = lean_ctor_get(v___x_4837_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4837_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4837_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_4984_, lean_object* v_optionsPerPos_4985_, lean_object* v_delab_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_4984_, v_optionsPerPos_4985_, v_delab_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_4993_, lean_object* v_e_4994_, lean_object* v_optionsPerPos_4995_, lean_object* v_delab_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_4994_, v_optionsPerPos_4995_, v_delab_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5003_, lean_object* v_e_5004_, lean_object* v_optionsPerPos_5005_, lean_object* v_delab_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5003_, v_e_5004_, v_optionsPerPos_5005_, v_delab_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5014_, lean_object* v_optionsPerPos_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5022_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5014_, v_optionsPerPos_5015_, v___x_5021_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5031_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5025_ = v___x_5022_;
v_isShared_5026_ = v_isSharedCheck_5031_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5022_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5031_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v_fst_5027_; lean_object* v___x_5029_; 
v_fst_5027_ = lean_ctor_get(v_a_5023_, 0);
lean_inc(v_fst_5027_);
lean_dec(v_a_5023_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v_fst_5027_);
v___x_5029_ = v___x_5025_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_fst_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
v_a_5032_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_5022_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5022_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5040_, lean_object* v_optionsPerPos_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_PrettyPrinter_delab(v_e_5040_, v_optionsPerPos_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5112_; uint8_t v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5112_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5113_ = 0;
v___x_5114_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5115_ = l_Lean_registerTraceClass(v___x_5112_, v___x_5113_, v___x_5114_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec_ref(v___x_5115_);
v___x_5116_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5117_ = l_Lean_registerTraceClass(v___x_5116_, v___x_5113_, v___x_5114_);
return v___x_5117_;
}
else
{
return v___x_5115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5119_;
}
}
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
