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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getInfo_x3f(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_getPPMaxSteps___boxed(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_getPPDeepTerms___boxed(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_maxChildren;
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPDeepTermsThreshold___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_getPPProofsWithType___boxed(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "delabFailure"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 138, 190, 155, 112, 230, 57, 130)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "builtin_delab"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 78, 157, 22, 7, 109, 94, 150)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delab"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 48, 28, 192, 106, 44, 69, 249)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Register a delaborator"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Delaborator"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 145, 52, 44, 66, 160, 163, 69)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "delabAttribute"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 105, 4, 51, 2, 59, 203, 237)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 513, .m_capacity = 513, .m_length = 512, .m_data = "Registers a delaborator.\n\n`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the\n`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`, elaborators\nfor `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\") to reduce\nspecial casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first.\n"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(124) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "attrApp_delab_"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(231, 152, 1, 212, 81, 225, 23, 202)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Register an unexpander for applications of a given constant."};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unexpander"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "appUnexpanderAttribute"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 177, 70, 181, 38, 19, 76, 236)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 620, .m_capacity = 620, .m_length = 619, .m_data = "Registers an unexpander for applications of a given constant.\n\n`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant\n`c`. The unexpander is passed the result of pre-pretty printing the application *without*\nimplicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,\nit will not be called at all.\n\nUnexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without\nspecial imports. This however also makes them much less capable since they can only transform\nsyntax and don't have access to the expression tree.\n"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(453) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(466) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(466) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(104, 172, 119, 199, 92, 54, 86, 47)}};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_delab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_delab___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_delab___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 19, 214, 208, 28, 243, 5, 52)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 164, 190, 165, 103, 227, 105, 51)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 183, 224, 255, 20, 2, 99, 61)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 0, 36, 13, 230, 137, 208, 68)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 99, 145, 72, 150, 13, 224, 205)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 207, 248, 169, 211, 175, 254, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 170, 24, 58, 43, 56, 104, 232)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 123, 18, 109, 183, 228, 66, 1)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 193, 243, 64, 48, 31, 65, 146)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 168, 97, 241, 156, 42, 72, 1)}};
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_));
v___x_6_ = l_Lean_registerInternalExceptionId(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
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
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
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
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
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
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref(v___x_43_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_8(v_d_u2082_35_, v___x_50_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_51_;
}
}
}
else
{
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
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
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
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
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
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
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v___x_74_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_8(v_d_u2082_66_, v___x_81_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, lean_box(0));
return v___x_82_;
}
}
}
else
{
lean_dec(v_a_75_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
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
v___x_122_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_122_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0);
v___x_124_ = l_ReaderT_instMonad___redArg(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM(void){
_start:
{
lean_object* v___x_131_; lean_object* v_toApplicative_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_213_; 
v___x_131_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
v_toApplicative_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v___x_131_, 1);
lean_dec(v_unused_214_);
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_213_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_toApplicative_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_213_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_toFunctor_136_; lean_object* v_toSeq_137_; lean_object* v_toSeqLeft_138_; lean_object* v_toSeqRight_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_211_; 
v_toFunctor_136_ = lean_ctor_get(v_toApplicative_132_, 0);
v_toSeq_137_ = lean_ctor_get(v_toApplicative_132_, 2);
v_toSeqLeft_138_ = lean_ctor_get(v_toApplicative_132_, 3);
v_toSeqRight_139_ = lean_ctor_get(v_toApplicative_132_, 4);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toApplicative_132_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_dec(v_unused_212_);
v___x_141_ = v_toApplicative_132_;
v_isShared_142_ = v_isSharedCheck_211_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_toSeqRight_139_);
lean_inc(v_toSeqLeft_138_);
lean_inc(v_toSeq_137_);
lean_inc(v_toFunctor_136_);
lean_dec(v_toApplicative_132_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_211_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_152_; 
v___f_143_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2));
v___f_144_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3));
lean_inc_ref(v_toFunctor_136_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_145_, 0, v_toFunctor_136_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_146_, 0, v_toFunctor_136_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___f_145_);
lean_ctor_set(v___x_147_, 1, v___f_146_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeqRight_139_);
v___f_149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_149_, 0, v_toSeqLeft_138_);
v___f_150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_150_, 0, v_toSeq_137_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 4, v___f_148_);
lean_ctor_set(v___x_141_, 3, v___f_149_);
lean_ctor_set(v___x_141_, 2, v___f_150_);
lean_ctor_set(v___x_141_, 1, v___f_143_);
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_152_ = v___x_141_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___f_143_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___f_150_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v___f_149_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v___f_148_);
v___x_152_ = v_reuseFailAlloc_210_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_154_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___f_144_);
lean_ctor_set(v___x_134_, 0, v___x_152_);
v___x_154_ = v___x_134_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___f_144_);
v___x_154_ = v_reuseFailAlloc_209_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v_toApplicative_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_207_; 
v___x_155_ = l_ReaderT_instMonad___redArg(v___x_154_);
v_toApplicative_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v___x_155_, 1);
lean_dec(v_unused_208_);
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_207_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_toApplicative_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_207_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_toFunctor_160_; lean_object* v_toSeq_161_; lean_object* v_toSeqLeft_162_; lean_object* v_toSeqRight_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_205_; 
v_toFunctor_160_ = lean_ctor_get(v_toApplicative_156_, 0);
v_toSeq_161_ = lean_ctor_get(v_toApplicative_156_, 2);
v_toSeqLeft_162_ = lean_ctor_get(v_toApplicative_156_, 3);
v_toSeqRight_163_ = lean_ctor_get(v_toApplicative_156_, 4);
v_isSharedCheck_205_ = !lean_is_exclusive(v_toApplicative_156_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_toApplicative_156_, 1);
lean_dec(v_unused_206_);
v___x_165_ = v_toApplicative_156_;
v_isShared_166_ = v_isSharedCheck_205_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_toSeqRight_163_);
lean_inc(v_toSeqLeft_162_);
lean_inc(v_toSeq_161_);
lean_inc(v_toFunctor_160_);
lean_dec(v_toApplicative_156_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_205_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_176_; 
v___f_167_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4));
v___f_168_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5));
lean_inc_ref(v_toFunctor_160_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_169_, 0, v_toFunctor_160_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_170_, 0, v_toFunctor_160_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___f_169_);
lean_ctor_set(v___x_171_, 1, v___f_170_);
v___f_172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_172_, 0, v_toSeqRight_163_);
v___f_173_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_173_, 0, v_toSeqLeft_162_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_174_, 0, v_toSeq_161_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v___f_172_);
lean_ctor_set(v___x_165_, 3, v___f_173_);
lean_ctor_set(v___x_165_, 2, v___f_174_);
lean_ctor_set(v___x_165_, 1, v___f_167_);
lean_ctor_set(v___x_165_, 0, v___x_171_);
v___x_176_ = v___x_165_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___f_167_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___f_174_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___f_173_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v___f_172_);
v___x_176_ = v_reuseFailAlloc_204_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___f_168_);
lean_ctor_set(v___x_158_, 0, v___x_176_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___f_168_);
v___x_178_ = v_reuseFailAlloc_203_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v_toApplicative_180_; lean_object* v_toFunctor_181_; lean_object* v_toSeq_182_; lean_object* v_toSeqLeft_183_; lean_object* v_toSeqRight_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_201_; 
v___x_179_ = l_ReaderT_instMonad___redArg(v___x_178_);
v_toApplicative_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_toApplicative_180_);
v_toFunctor_181_ = lean_ctor_get(v_toApplicative_180_, 0);
v_toSeq_182_ = lean_ctor_get(v_toApplicative_180_, 2);
v_toSeqLeft_183_ = lean_ctor_get(v_toApplicative_180_, 3);
v_toSeqRight_184_ = lean_ctor_get(v_toApplicative_180_, 4);
v_isSharedCheck_201_ = !lean_is_exclusive(v_toApplicative_180_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_dec(v_unused_202_);
v___x_186_ = v_toApplicative_180_;
v_isShared_187_ = v_isSharedCheck_201_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_toSeqRight_184_);
lean_inc(v_toSeqLeft_183_);
lean_inc(v_toSeq_182_);
lean_inc(v_toFunctor_181_);
lean_dec(v_toApplicative_180_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_201_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_188_, 0, v_toSeqRight_184_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_189_, 0, v_toSeqLeft_183_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_190_, 0, v_toSeq_182_);
lean_inc_ref(v_toFunctor_181_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_191_, 0, v_toFunctor_181_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_192_, 0, v_toFunctor_181_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___f_191_);
lean_ctor_set(v___x_193_, 1, v___f_192_);
v___x_194_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_194_, 0, lean_box(0));
lean_closure_set(v___x_194_, 1, lean_box(0));
lean_closure_set(v___x_194_, 2, v___x_179_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 4, v___f_188_);
lean_ctor_set(v___x_186_, 3, v___f_189_);
lean_ctor_set(v___x_186_, 2, v___f_190_);
lean_ctor_set(v___x_186_, 1, v___x_194_);
lean_ctor_set(v___x_186_, 0, v___x_193_);
v___x_196_ = v___x_186_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___f_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___f_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v___f_188_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6));
v___x_198_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7));
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v___x_196_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_198_);
return v___x_199_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* v_00_u03b1_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_subExpr_225_; lean_object* v___x_226_; 
v_subExpr_225_ = lean_ctor_get(v___y_218_, 3);
lean_inc_ref(v_subExpr_225_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_subExpr_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed(lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(lean_object* v_00_u03b1_237_, lean_object* v_f_238_, lean_object* v_x_239_, lean_object* v_ctx_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_optionsPerPos_247_; lean_object* v_currNamespace_248_; lean_object* v_openDecls_249_; uint8_t v_inPattern_250_; lean_object* v_subExpr_251_; lean_object* v_depth_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_261_; 
v_optionsPerPos_247_ = lean_ctor_get(v_ctx_240_, 0);
v_currNamespace_248_ = lean_ctor_get(v_ctx_240_, 1);
v_openDecls_249_ = lean_ctor_get(v_ctx_240_, 2);
v_inPattern_250_ = lean_ctor_get_uint8(v_ctx_240_, sizeof(void*)*5);
v_subExpr_251_ = lean_ctor_get(v_ctx_240_, 3);
v_depth_252_ = lean_ctor_get(v_ctx_240_, 4);
v_isSharedCheck_261_ = !lean_is_exclusive(v_ctx_240_);
if (v_isSharedCheck_261_ == 0)
{
v___x_254_ = v_ctx_240_;
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_depth_252_);
lean_inc(v_subExpr_251_);
lean_inc(v_openDecls_249_);
lean_inc(v_currNamespace_248_);
lean_inc(v_optionsPerPos_247_);
lean_dec(v_ctx_240_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_apply_1(v_f_238_, v_subExpr_251_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_optionsPerPos_247_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_currNamespace_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_openDecls_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_depth_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_260_, sizeof(void*)*5, v_inPattern_250_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_apply_7(v_x_239_, v___x_258_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object* v_00_u03b1_262_, lean_object* v_f_263_, lean_object* v_x_264_, lean_object* v_ctx_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(v_00_u03b1_262_, v_f_263_, v_x_264_, v_ctx_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_holeIter_283_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_get(v___y_276_);
v_holeIter_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc_ref(v_holeIter_283_);
lean_dec(v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_holeIter_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object* v_iter_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_steps_302_; lean_object* v_infos_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v___x_301_ = lean_st_ref_take(v___y_295_);
v_steps_302_ = lean_ctor_get(v___x_301_, 0);
v_infos_303_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_301_, 2);
lean_dec(v_unused_314_);
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_infos_303_);
lean_inc(v_steps_302_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 2, v_iter_293_);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_steps_302_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_infos_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_iter_293_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_st_ref_set(v___y_295_, v___x_308_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object* v_iter_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(v_iter_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object* v_00_u03b1_324_, lean_object* v_f_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_steps_334_; lean_object* v_infos_335_; lean_object* v_holeIter_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_348_; 
v___x_333_ = lean_st_ref_take(v___y_327_);
v_steps_334_ = lean_ctor_get(v___x_333_, 0);
v_infos_335_ = lean_ctor_get(v___x_333_, 1);
v_holeIter_336_ = lean_ctor_get(v___x_333_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_348_ == 0)
{
v___x_338_ = v___x_333_;
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_holeIter_336_);
lean_inc(v_infos_335_);
lean_inc(v_steps_334_);
lean_dec(v___x_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_344_; 
v___x_340_ = lean_apply_1(v_f_325_, v_holeIter_336_);
v_fst_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v___x_340_, 1);
lean_inc(v_snd_342_);
lean_dec_ref(v___x_340_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 2, v_snd_342_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_steps_334_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_infos_335_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_snd_342_);
v___x_344_ = v_reuseFailAlloc_347_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_st_ref_set(v___y_327_, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_fst_341_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object* v_00_u03b1_349_, lean_object* v_f_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(v_00_u03b1_349_, v_f_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_builtin_367_, lean_object* v_declName_368_, lean_object* v_key_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_builtin_375_, lean_object* v_declName_376_, lean_object* v_key_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v_builtin_boxed_381_; lean_object* v_res_382_; 
v_builtin_boxed_381_ = lean_unbox(v_builtin_375_);
v_res_382_ = l_Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_builtin_boxed_381_, v_declName_376_, v_key_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_key_377_);
lean_dec(v_declName_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_cls_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_options_389_; uint8_t v_hasTrace_390_; 
v_options_389_ = lean_ctor_get(v___y_387_, 2);
v_hasTrace_390_ = lean_ctor_get_uint8(v_options_389_, sizeof(void*)*1);
if (v_hasTrace_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_cls_386_);
v___x_391_ = lean_box(v_hasTrace_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v_inheritedTraceOptions_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_inheritedTraceOptions_393_ = lean_ctor_get(v___y_387_, 13);
v___x_394_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_395_ = l_Lean_Name_append(v___x_394_, v_cls_386_);
v___x_396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_393_, v_options_389_, v___x_395_);
lean_dec(v___x_395_);
v___x_397_ = lean_box(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_cls_399_, v___y_400_);
lean_dec_ref(v___y_400_);
return v_res_402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_keys_403_, lean_object* v_i_404_, lean_object* v_k_405_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_array_get_size(v_keys_403_);
v___x_407_ = lean_nat_dec_lt(v_i_404_, v___x_406_);
if (v___x_407_ == 0)
{
lean_dec(v_i_404_);
return v___x_407_;
}
else
{
lean_object* v_k_x27_408_; uint8_t v___x_409_; 
v_k_x27_408_ = lean_array_fget_borrowed(v_keys_403_, v_i_404_);
v___x_409_ = l_Lean_instBEqExtraModUse_beq(v_k_405_, v_k_x27_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_i_404_, v___x_410_);
lean_dec(v_i_404_);
v_i_404_ = v___x_411_;
goto _start;
}
else
{
lean_dec(v_i_404_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_keys_413_, lean_object* v_i_414_, lean_object* v_k_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_413_, v_i_414_, v_k_415_);
lean_dec_ref(v_k_415_);
lean_dec_ref(v_keys_413_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; 
v___x_418_ = ((size_t)5ULL);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_shift_left(v___x_419_, v___x_418_);
return v___x_420_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_423_ = lean_usize_sub(v___x_422_, v___x_421_);
return v___x_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_424_, size_t v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v_es_427_; lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v_j_432_; lean_object* v___x_433_; 
v_es_427_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_es_427_);
lean_dec_ref(v_x_424_);
v___x_428_ = lean_box(2);
v___x_429_ = ((size_t)5ULL);
v___x_430_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_431_ = lean_usize_land(v_x_425_, v___x_430_);
v_j_432_ = lean_usize_to_nat(v___x_431_);
v___x_433_ = lean_array_get(v___x_428_, v_es_427_, v_j_432_);
lean_dec(v_j_432_);
lean_dec_ref(v_es_427_);
switch(lean_obj_tag(v___x_433_))
{
case 0:
{
lean_object* v_key_434_; uint8_t v___x_435_; 
v_key_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_key_434_);
lean_dec_ref(v___x_433_);
v___x_435_ = l_Lean_instBEqExtraModUse_beq(v_x_426_, v_key_434_);
lean_dec(v_key_434_);
return v___x_435_;
}
case 1:
{
lean_object* v_node_436_; size_t v___x_437_; 
v_node_436_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_node_436_);
lean_dec_ref(v___x_433_);
v___x_437_ = lean_usize_shift_right(v_x_425_, v___x_429_);
v_x_424_ = v_node_436_;
v_x_425_ = v___x_437_;
goto _start;
}
default: 
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
}
}
else
{
lean_object* v_ks_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_ks_440_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_ks_440_);
lean_dec_ref(v_x_424_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_ks_440_, v___x_441_, v_x_426_);
lean_dec_ref(v_ks_440_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
size_t v_x_7292__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_x_7292__boxed_446_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_res_447_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_443_, v_x_7292__boxed_446_, v_x_445_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
uint64_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = l_Lean_instHashableExtraModUse_hash(v_x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_449_, v___x_452_, v_x_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_454_, v_x_455_);
lean_dec_ref(v_x_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_458_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__0);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
lean_ctor_set(v___x_463_, 3, v___x_461_);
lean_ctor_set(v___x_463_, 4, v___x_461_);
lean_ctor_set(v___x_463_, 5, v___x_461_);
lean_ctor_set(v___x_463_, 6, v___x_461_);
lean_ctor_set(v___x_463_, 7, v___x_461_);
lean_ctor_set(v___x_463_, 8, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(32u);
v___x_465_ = lean_mk_empty_array_with_capacity(v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4(void){
_start:
{
size_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_467_ = ((size_t)5ULL);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_unsigned_to_nat(32u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__3);
v___x_472_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_468_);
lean_ctor_set(v___x_472_, 3, v___x_468_);
lean_ctor_set_usize(v___x_472_, 4, v___x_467_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_box(1);
v___x_474_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__4);
v___x_475_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__1);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_473_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6(lean_object* v_msgData_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_env_482_; lean_object* v_options_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_481_ = lean_st_ref_get(v___y_479_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_env_482_);
lean_dec(v___x_481_);
v_options_483_ = lean_ctor_get(v___y_478_, 2);
v___x_484_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2);
v___x_485_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5);
lean_inc_ref(v_options_483_);
v___x_486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_486_, 0, v_env_482_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
lean_ctor_set(v___x_486_, 3, v_options_483_);
v___x_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_msgData_477_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6(v_msgData_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_493_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_494_; double v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_float_of_nat(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object* v_cls_499_, lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_ref_504_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_550_; 
v_ref_504_ = lean_ctor_get(v___y_501_, 5);
v___x_505_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6(v_msg_500_, v___y_501_, v___y_502_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_550_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_550_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_550_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_traceState_511_; lean_object* v_env_512_; lean_object* v_nextMacroScope_513_; lean_object* v_ngen_514_; lean_object* v_auxDeclNGen_515_; lean_object* v_cache_516_; lean_object* v_messages_517_; lean_object* v_infoState_518_; lean_object* v_snapshotTasks_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_549_; 
v___x_510_ = lean_st_ref_take(v___y_502_);
v_traceState_511_ = lean_ctor_get(v___x_510_, 4);
v_env_512_ = lean_ctor_get(v___x_510_, 0);
v_nextMacroScope_513_ = lean_ctor_get(v___x_510_, 1);
v_ngen_514_ = lean_ctor_get(v___x_510_, 2);
v_auxDeclNGen_515_ = lean_ctor_get(v___x_510_, 3);
v_cache_516_ = lean_ctor_get(v___x_510_, 5);
v_messages_517_ = lean_ctor_get(v___x_510_, 6);
v_infoState_518_ = lean_ctor_get(v___x_510_, 7);
v_snapshotTasks_519_ = lean_ctor_get(v___x_510_, 8);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_549_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_549_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snapshotTasks_519_);
lean_inc(v_infoState_518_);
lean_inc(v_messages_517_);
lean_inc(v_cache_516_);
lean_inc(v_traceState_511_);
lean_inc(v_auxDeclNGen_515_);
lean_inc(v_ngen_514_);
lean_inc(v_nextMacroScope_513_);
lean_inc(v_env_512_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_549_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint64_t v_tid_523_; lean_object* v_traces_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_548_; 
v_tid_523_ = lean_ctor_get_uint64(v_traceState_511_, sizeof(void*)*1);
v_traces_524_ = lean_ctor_get(v_traceState_511_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_traceState_511_);
if (v_isSharedCheck_548_ == 0)
{
v___x_526_ = v_traceState_511_;
v_isShared_527_ = v_isSharedCheck_548_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_traces_524_);
lean_dec(v_traceState_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_548_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; double v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_528_ = lean_box(0);
v___x_529_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0);
v___x_530_ = 0;
v___x_531_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1));
v___x_532_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_532_, 0, v_cls_499_);
lean_ctor_set(v___x_532_, 1, v___x_528_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
lean_ctor_set_float(v___x_532_, sizeof(void*)*3, v___x_529_);
lean_ctor_set_float(v___x_532_, sizeof(void*)*3 + 8, v___x_529_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3 + 16, v___x_530_);
v___x_533_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__2));
v___x_534_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v_a_506_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
lean_inc(v_ref_504_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_ref_504_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_PersistentArray_push___redArg(v_traces_524_, v___x_535_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_536_);
v___x_538_ = v___x_526_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_536_);
lean_ctor_set_uint64(v_reuseFailAlloc_547_, sizeof(void*)*1, v_tid_523_);
v___x_538_ = v_reuseFailAlloc_547_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___x_538_);
v___x_540_ = v___x_521_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_env_512_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_nextMacroScope_513_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_ngen_514_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_auxDeclNGen_515_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_cache_516_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_messages_517_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_infoState_518_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_snapshotTasks_519_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_st_ref_set(v___y_502_, v___x_540_);
v___x_542_ = lean_box(0);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_542_);
v___x_544_ = v___x_508_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object* v_cls_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_cls_551_, v_msg_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_556_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__1));
v___x_560_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_561_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_562_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__8));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__10));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__13));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__15));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_mod_588_, uint8_t v_isMeta_589_, lean_object* v_hint_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_env_595_; uint8_t v_isExporting_596_; lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v_entry_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___y_605_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_594_ = lean_st_ref_get(v___y_592_);
v_env_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc_ref(v_env_595_);
lean_dec(v___x_594_);
v_isExporting_596_ = lean_ctor_get_uint8(v_env_595_, sizeof(void*)*8);
lean_dec_ref(v_env_595_);
v___x_597_ = lean_st_ref_get(v___y_592_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__2);
lean_inc(v_mod_588_);
v_entry_600_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_600_, 0, v_mod_588_);
lean_ctor_set_uint8(v_entry_600_, sizeof(void*)*1, v_isExporting_596_);
lean_ctor_set_uint8(v_entry_600_, sizeof(void*)*1 + 1, v_isMeta_589_);
v___x_601_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_602_ = lean_box(1);
v___x_603_ = lean_box(0);
v___x_630_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_599_, v___x_601_, v_env_598_, v___x_602_, v___x_603_);
v___x_631_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_630_, v_entry_600_);
if (v___x_631_ == 0)
{
lean_object* v_cls_632_; lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v___x_654_; 
v_cls_632_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__7));
v___x_633_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_cls_632_, v___y_591_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_654_ = lean_unbox(v_a_634_);
lean_dec(v_a_634_);
if (v___x_654_ == 0)
{
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___y_605_ = v___y_592_;
goto v___jp_604_;
}
else
{
lean_object* v___x_655_; lean_object* v___y_657_; 
v___x_655_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__14);
if (v_isExporting_596_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__19));
v___y_657_ = v___x_664_;
goto v___jp_656_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__20));
v___y_657_ = v___x_665_;
goto v___jp_656_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_658_ = l_Lean_stringToMessageData(v___y_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_655_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__16);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
if (v_isMeta_589_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__17));
v___y_641_ = v___x_661_;
v___y_642_ = v___x_662_;
goto v___jp_640_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__18));
v___y_641_ = v___x_661_;
v___y_642_ = v___x_663_;
goto v___jp_640_;
}
}
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___y_636_);
lean_ctor_set(v___x_638_, 1, v___y_637_);
v___x_639_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_cls_632_, v___x_638_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref(v___x_639_);
v___y_605_ = v___y_592_;
goto v___jp_604_;
}
else
{
lean_dec_ref(v_entry_600_);
return v___x_639_;
}
}
v___jp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_643_ = l_Lean_stringToMessageData(v___y_642_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_641_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__9);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_MessageData_ofName(v_mod_588_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_Name_isAnonymous(v_hint_590_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__11);
v___x_651_ = l_Lean_MessageData_ofName(v_hint_590_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___y_636_ = v___x_648_;
v___y_637_ = v___x_652_;
goto v___jp_635_;
}
else
{
lean_object* v___x_653_; 
lean_dec(v_hint_590_);
v___x_653_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__12);
v___y_636_ = v___x_648_;
v___y_637_ = v___x_653_;
goto v___jp_635_;
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_entry_600_);
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v_toEnvExtension_607_; lean_object* v_env_608_; lean_object* v_nextMacroScope_609_; lean_object* v_ngen_610_; lean_object* v_auxDeclNGen_611_; lean_object* v_traceState_612_; lean_object* v_messages_613_; lean_object* v_infoState_614_; lean_object* v_snapshotTasks_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_628_; 
v___x_606_ = lean_st_ref_take(v___y_605_);
v_toEnvExtension_607_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_toEnvExtension_607_);
v_env_608_ = lean_ctor_get(v___x_606_, 0);
v_nextMacroScope_609_ = lean_ctor_get(v___x_606_, 1);
v_ngen_610_ = lean_ctor_get(v___x_606_, 2);
v_auxDeclNGen_611_ = lean_ctor_get(v___x_606_, 3);
v_traceState_612_ = lean_ctor_get(v___x_606_, 4);
v_messages_613_ = lean_ctor_get(v___x_606_, 6);
v_infoState_614_ = lean_ctor_get(v___x_606_, 7);
v_snapshotTasks_615_ = lean_ctor_get(v___x_606_, 8);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_606_, 5);
lean_dec(v_unused_629_);
v___x_617_ = v___x_606_;
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snapshotTasks_615_);
lean_inc(v_infoState_614_);
lean_inc(v_messages_613_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_611_);
lean_inc(v_ngen_610_);
lean_inc(v_nextMacroScope_609_);
lean_inc(v_env_608_);
lean_dec(v___x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_628_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_asyncMode_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_asyncMode_619_ = lean_ctor_get(v_toEnvExtension_607_, 2);
lean_inc(v_asyncMode_619_);
lean_dec_ref(v_toEnvExtension_607_);
v___x_620_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_601_, v_env_608_, v_entry_600_, v_asyncMode_619_, v___x_603_);
lean_dec(v_asyncMode_619_);
v___x_621_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 5, v___x_621_);
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_nextMacroScope_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_ngen_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_auxDeclNGen_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_traceState_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_messages_613_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_infoState_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_snapshotTasks_615_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_st_ref_set(v___y_605_, v___x_623_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_mod_668_, lean_object* v_isMeta_669_, lean_object* v_hint_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v_isMeta_boxed_674_; lean_object* v_res_675_; 
v_isMeta_boxed_674_ = lean_unbox(v_isMeta_669_);
v_res_675_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_mod_668_, v_isMeta_boxed_674_, v_hint_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(lean_object* v___x_676_, lean_object* v_declName_677_, lean_object* v_as_678_, size_t v_sz_679_, size_t v_i_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v_declName_677_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_b_681_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v_modules_688_; lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v_toImport_692_; lean_object* v_module_693_; uint8_t v___x_694_; lean_object* v___x_695_; 
v___x_687_ = l_Lean_Environment_header(v___x_676_);
v_modules_688_ = lean_ctor_get(v___x_687_, 3);
lean_inc_ref(v_modules_688_);
lean_dec_ref(v___x_687_);
v___x_689_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_690_ = lean_array_uget_borrowed(v_as_678_, v_i_680_);
v___x_691_ = lean_array_get(v___x_689_, v_modules_688_, v_a_690_);
lean_dec_ref(v_modules_688_);
v_toImport_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_toImport_692_);
lean_dec(v___x_691_);
v_module_693_ = lean_ctor_get(v_toImport_692_, 0);
lean_inc(v_module_693_);
lean_dec_ref(v_toImport_692_);
v___x_694_ = 0;
lean_inc(v_declName_677_);
v___x_695_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_693_, v___x_694_, v_declName_677_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; size_t v___x_697_; size_t v___x_698_; 
lean_dec_ref(v___x_695_);
v___x_696_ = lean_box(0);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_680_, v___x_697_);
v_i_680_ = v___x_698_;
v_b_681_ = v___x_696_;
goto _start;
}
else
{
lean_dec(v_declName_677_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v___x_700_, lean_object* v_declName_701_, lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_710_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v___x_700_, v_declName_701_, v_as_702_, v_sz_boxed_709_, v_i_boxed_710_, v_b_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_as_702_);
lean_dec_ref(v___x_700_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg(lean_object* v_a_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
else
{
lean_object* v_key_715_; lean_object* v_value_716_; lean_object* v_tail_717_; uint8_t v___x_718_; 
v_key_715_ = lean_ctor_get(v_x_713_, 0);
v_value_716_ = lean_ctor_get(v_x_713_, 1);
v_tail_717_ = lean_ctor_get(v_x_713_, 2);
v___x_718_ = lean_name_eq(v_key_715_, v_a_712_);
if (v___x_718_ == 0)
{
v_x_713_ = v_tail_717_;
goto _start;
}
else
{
lean_object* v___x_720_; 
lean_inc(v_value_716_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_value_716_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg(v_a_721_, v_x_722_);
lean_dec(v_x_722_);
lean_dec(v_a_721_);
return v_res_723_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_724_; uint64_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1723u);
v___x_725_ = lean_uint64_of_nat(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_m_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_buckets_728_; lean_object* v___x_729_; uint64_t v___y_731_; 
v_buckets_728_ = lean_ctor_get(v_m_726_, 1);
v___x_729_ = lean_array_get_size(v_buckets_728_);
if (lean_obj_tag(v_a_727_) == 0)
{
uint64_t v___x_745_; 
v___x_745_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___closed__0);
v___y_731_ = v___x_745_;
goto v___jp_730_;
}
else
{
uint64_t v_hash_746_; 
v_hash_746_ = lean_ctor_get_uint64(v_a_727_, sizeof(void*)*2);
v___y_731_ = v_hash_746_;
goto v___jp_730_;
}
v___jp_730_:
{
uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v_fold_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_732_ = 32ULL;
v___x_733_ = lean_uint64_shift_right(v___y_731_, v___x_732_);
v_fold_734_ = lean_uint64_xor(v___y_731_, v___x_733_);
v___x_735_ = 16ULL;
v___x_736_ = lean_uint64_shift_right(v_fold_734_, v___x_735_);
v___x_737_ = lean_uint64_xor(v_fold_734_, v___x_736_);
v___x_738_ = lean_uint64_to_usize(v___x_737_);
v___x_739_ = lean_usize_of_nat(v___x_729_);
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_sub(v___x_739_, v___x_740_);
v___x_742_ = lean_usize_land(v___x_738_, v___x_741_);
v___x_743_ = lean_array_uget_borrowed(v_buckets_728_, v___x_742_);
v___x_744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg(v_a_727_, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_m_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__1));
v___x_753_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__0));
v___x_754_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_753_, v___x_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(lean_object* v_declName_757_, uint8_t v_isMeta_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_env_766_; lean_object* v___y_768_; lean_object* v___x_781_; 
v___x_762_ = lean_st_ref_get(v___y_760_);
v_env_766_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_env_766_);
lean_dec(v___x_762_);
v___x_781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_766_, v_declName_757_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_dec_ref(v_env_766_);
lean_dec(v_declName_757_);
goto v___jp_763_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_783_; lean_object* v_modules_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Lean_Environment_header(v_env_766_);
v_modules_784_ = lean_ctor_get(v___x_783_, 3);
lean_inc_ref(v_modules_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_array_get_size(v_modules_784_);
v___x_786_ = lean_nat_dec_lt(v_val_782_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v_modules_784_);
lean_dec(v_val_782_);
lean_dec_ref(v_env_766_);
lean_dec(v_declName_757_);
goto v___jp_763_;
}
else
{
lean_object* v___x_787_; lean_object* v_env_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___y_792_; 
v___x_787_ = lean_st_ref_get(v___y_760_);
v_env_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_787_);
v___x_789_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__2);
v___x_790_ = lean_array_fget(v_modules_784_, v_val_782_);
lean_dec(v_val_782_);
lean_dec_ref(v_modules_784_);
if (v_isMeta_758_ == 0)
{
lean_dec_ref(v_env_788_);
v___y_792_ = v_isMeta_758_;
goto v___jp_791_;
}
else
{
uint8_t v___x_803_; 
lean_inc(v_declName_757_);
v___x_803_ = l_Lean_isMarkedMeta(v_env_788_, v_declName_757_);
if (v___x_803_ == 0)
{
v___y_792_ = v_isMeta_758_;
goto v___jp_791_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = 0;
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v_toImport_793_; lean_object* v_module_794_; lean_object* v___x_795_; 
v_toImport_793_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_toImport_793_);
lean_dec(v___x_790_);
v_module_794_ = lean_ctor_get(v_toImport_793_, 0);
lean_inc(v_module_794_);
lean_dec_ref(v_toImport_793_);
lean_inc(v_declName_757_);
v___x_795_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0(v_module_794_, v___y_792_, v_declName_757_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___x_795_);
v___x_796_ = l_Lean_indirectModUseExt;
v___x_797_ = lean_box(1);
v___x_798_ = lean_box(0);
lean_inc_ref(v_env_766_);
v___x_799_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_789_, v___x_796_, v_env_766_, v___x_797_, v___x_798_);
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_799_, v_declName_757_);
lean_dec(v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___closed__3));
v___y_768_ = v___x_801_;
goto v___jp_767_;
}
else
{
lean_object* v_val_802_; 
v_val_802_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_val_802_);
lean_dec_ref(v___x_800_);
v___y_768_ = v_val_802_;
goto v___jp_767_;
}
}
else
{
lean_dec_ref(v_env_766_);
lean_dec(v_declName_757_);
return v___x_795_;
}
}
}
}
v___jp_763_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
v___jp_767_:
{
lean_object* v___x_769_; size_t v_sz_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_769_ = lean_box(0);
v_sz_770_ = lean_array_size(v___y_768_);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__1(v_env_766_, v_declName_757_, v___y_768_, v_sz_770_, v___x_771_, v___x_769_, v___y_759_, v___y_760_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_env_766_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_772_, 0);
lean_dec(v_unused_780_);
v___x_774_ = v___x_772_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_772_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_769_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_769_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0___boxed(lean_object* v_declName_805_, lean_object* v_isMeta_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_isMeta_boxed_810_; lean_object* v_res_811_; 
v_isMeta_boxed_810_ = lean_unbox(v_isMeta_806_);
v_res_811_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_declName_805_, v_isMeta_boxed_810_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg(lean_object* v_t_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_infoState_816_; uint8_t v_enabled_817_; 
v___x_815_ = lean_st_ref_get(v___y_813_);
v_infoState_816_ = lean_ctor_get(v___x_815_, 7);
lean_inc_ref(v_infoState_816_);
lean_dec(v___x_815_);
v_enabled_817_ = lean_ctor_get_uint8(v_infoState_816_, sizeof(void*)*3);
lean_dec_ref(v_infoState_816_);
if (v_enabled_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_t_812_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; lean_object* v_infoState_821_; lean_object* v_env_822_; lean_object* v_nextMacroScope_823_; lean_object* v_ngen_824_; lean_object* v_auxDeclNGen_825_; lean_object* v_traceState_826_; lean_object* v_cache_827_; lean_object* v_messages_828_; lean_object* v_snapshotTasks_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_851_; 
v___x_820_ = lean_st_ref_take(v___y_813_);
v_infoState_821_ = lean_ctor_get(v___x_820_, 7);
v_env_822_ = lean_ctor_get(v___x_820_, 0);
v_nextMacroScope_823_ = lean_ctor_get(v___x_820_, 1);
v_ngen_824_ = lean_ctor_get(v___x_820_, 2);
v_auxDeclNGen_825_ = lean_ctor_get(v___x_820_, 3);
v_traceState_826_ = lean_ctor_get(v___x_820_, 4);
v_cache_827_ = lean_ctor_get(v___x_820_, 5);
v_messages_828_ = lean_ctor_get(v___x_820_, 6);
v_snapshotTasks_829_ = lean_ctor_get(v___x_820_, 8);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_851_ == 0)
{
v___x_831_ = v___x_820_;
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_snapshotTasks_829_);
lean_inc(v_infoState_821_);
lean_inc(v_messages_828_);
lean_inc(v_cache_827_);
lean_inc(v_traceState_826_);
lean_inc(v_auxDeclNGen_825_);
lean_inc(v_ngen_824_);
lean_inc(v_nextMacroScope_823_);
lean_inc(v_env_822_);
lean_dec(v___x_820_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v_enabled_833_; lean_object* v_assignment_834_; lean_object* v_lazyAssignment_835_; lean_object* v_trees_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_850_; 
v_enabled_833_ = lean_ctor_get_uint8(v_infoState_821_, sizeof(void*)*3);
v_assignment_834_ = lean_ctor_get(v_infoState_821_, 0);
v_lazyAssignment_835_ = lean_ctor_get(v_infoState_821_, 1);
v_trees_836_ = lean_ctor_get(v_infoState_821_, 2);
v_isSharedCheck_850_ = !lean_is_exclusive(v_infoState_821_);
if (v_isSharedCheck_850_ == 0)
{
v___x_838_ = v_infoState_821_;
v_isShared_839_ = v_isSharedCheck_850_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_trees_836_);
lean_inc(v_lazyAssignment_835_);
lean_inc(v_assignment_834_);
lean_dec(v_infoState_821_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_850_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_PersistentArray_push___redArg(v_trees_836_, v_t_812_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 2, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_assignment_834_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_lazyAssignment_835_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v___x_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*3, v_enabled_833_);
v___x_842_ = v_reuseFailAlloc_849_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 7, v___x_842_);
v___x_844_ = v___x_831_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_env_822_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_nextMacroScope_823_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_ngen_824_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_auxDeclNGen_825_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v_traceState_826_);
lean_ctor_set(v_reuseFailAlloc_848_, 5, v_cache_827_);
lean_ctor_set(v_reuseFailAlloc_848_, 6, v_messages_828_);
lean_ctor_set(v_reuseFailAlloc_848_, 7, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 8, v_snapshotTasks_829_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_st_ref_set(v___y_813_, v___x_844_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_t_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg(v_t_852_, v___y_853_);
lean_dec(v___y_853_);
return v_res_855_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_unsigned_to_nat(32u);
v___x_857_ = lean_mk_empty_array_with_capacity(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_859_ = ((size_t)5ULL);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_unsigned_to_nat(32u);
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_861_);
v___x_863_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__0);
v___x_864_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_860_);
lean_ctor_set(v___x_864_, 3, v___x_860_);
lean_ctor_set_usize(v___x_864_, 4, v___x_859_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_t_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_infoState_870_; uint8_t v_enabled_871_; 
v___x_869_ = lean_st_ref_get(v___y_867_);
v_infoState_870_ = lean_ctor_get(v___x_869_, 7);
lean_inc_ref(v_infoState_870_);
lean_dec(v___x_869_);
v_enabled_871_ = lean_ctor_get_uint8(v_infoState_870_, sizeof(void*)*3);
lean_dec_ref(v_infoState_870_);
if (v_enabled_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_t_865_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___closed__1);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v_t_865_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg(v___x_875_, v___y_867_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_t_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v_t_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__10(lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l_List_reverse___redArg(v_a_883_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_895_; 
v_head_885_ = lean_ctor_get(v_a_882_, 0);
v_tail_886_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_888_ = v_a_882_;
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec(v_a_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_mkLevelParam(v_head_885_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_a_883_);
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_a_883_);
v___x_892_ = v_reuseFailAlloc_894_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
v_a_882_ = v_tail_886_;
v_a_883_ = v___x_892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_ref_900_; lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_910_; 
v_ref_900_ = lean_ctor_get(v___y_897_, 5);
v___x_901_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6(v_msg_896_, v___y_897_, v___y_898_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_910_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_inc(v_ref_900_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_ref_900_);
lean_ctor_set(v___x_906_, 1, v_a_902_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 1);
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_916_, lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_fileName_921_; lean_object* v_fileMap_922_; lean_object* v_options_923_; lean_object* v_currRecDepth_924_; lean_object* v_maxRecDepth_925_; lean_object* v_ref_926_; lean_object* v_currNamespace_927_; lean_object* v_openDecls_928_; lean_object* v_initHeartbeats_929_; lean_object* v_maxHeartbeats_930_; lean_object* v_quotContext_931_; lean_object* v_currMacroScope_932_; uint8_t v_diag_933_; lean_object* v_cancelTk_x3f_934_; uint8_t v_suppressElabErrors_935_; lean_object* v_inheritedTraceOptions_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
v_fileName_921_ = lean_ctor_get(v___y_918_, 0);
v_fileMap_922_ = lean_ctor_get(v___y_918_, 1);
v_options_923_ = lean_ctor_get(v___y_918_, 2);
v_currRecDepth_924_ = lean_ctor_get(v___y_918_, 3);
v_maxRecDepth_925_ = lean_ctor_get(v___y_918_, 4);
v_ref_926_ = lean_ctor_get(v___y_918_, 5);
v_currNamespace_927_ = lean_ctor_get(v___y_918_, 6);
v_openDecls_928_ = lean_ctor_get(v___y_918_, 7);
v_initHeartbeats_929_ = lean_ctor_get(v___y_918_, 8);
v_maxHeartbeats_930_ = lean_ctor_get(v___y_918_, 9);
v_quotContext_931_ = lean_ctor_get(v___y_918_, 10);
v_currMacroScope_932_ = lean_ctor_get(v___y_918_, 11);
v_diag_933_ = lean_ctor_get_uint8(v___y_918_, sizeof(void*)*14);
v_cancelTk_x3f_934_ = lean_ctor_get(v___y_918_, 12);
v_suppressElabErrors_935_ = lean_ctor_get_uint8(v___y_918_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_936_ = lean_ctor_get(v___y_918_, 13);
v_isSharedCheck_945_ = !lean_is_exclusive(v___y_918_);
if (v_isSharedCheck_945_ == 0)
{
v___x_938_ = v___y_918_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_inheritedTraceOptions_936_);
lean_inc(v_cancelTk_x3f_934_);
lean_inc(v_currMacroScope_932_);
lean_inc(v_quotContext_931_);
lean_inc(v_maxHeartbeats_930_);
lean_inc(v_initHeartbeats_929_);
lean_inc(v_openDecls_928_);
lean_inc(v_currNamespace_927_);
lean_inc(v_ref_926_);
lean_inc(v_maxRecDepth_925_);
lean_inc(v_currRecDepth_924_);
lean_inc(v_options_923_);
lean_inc(v_fileMap_922_);
lean_inc(v_fileName_921_);
lean_dec(v___y_918_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_ref_940_; lean_object* v___x_942_; 
v_ref_940_ = l_Lean_replaceRef(v_ref_916_, v_ref_926_);
lean_dec(v_ref_926_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 5, v_ref_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_fileName_921_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_fileMap_922_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_options_923_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_currRecDepth_924_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_maxRecDepth_925_);
lean_ctor_set(v_reuseFailAlloc_944_, 5, v_ref_940_);
lean_ctor_set(v_reuseFailAlloc_944_, 6, v_currNamespace_927_);
lean_ctor_set(v_reuseFailAlloc_944_, 7, v_openDecls_928_);
lean_ctor_set(v_reuseFailAlloc_944_, 8, v_initHeartbeats_929_);
lean_ctor_set(v_reuseFailAlloc_944_, 9, v_maxHeartbeats_930_);
lean_ctor_set(v_reuseFailAlloc_944_, 10, v_quotContext_931_);
lean_ctor_set(v_reuseFailAlloc_944_, 11, v_currMacroScope_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 12, v_cancelTk_x3f_934_);
lean_ctor_set(v_reuseFailAlloc_944_, 13, v_inheritedTraceOptions_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*14, v_diag_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*14 + 1, v_suppressElabErrors_935_);
v___x_942_ = v_reuseFailAlloc_944_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_917_, v___x_942_, v___y_919_);
lean_dec_ref(v___x_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_946_, lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg(v_ref_946_, v_msg_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec(v_ref_946_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__2));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__4));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_973_, lean_object* v_declHint_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_env_978_; uint8_t v___x_979_; 
v___x_977_ = lean_st_ref_get(v___y_975_);
v_env_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_977_);
v___x_979_ = l_Lean_Name_isAnonymous(v_declHint_974_);
if (v___x_979_ == 0)
{
uint8_t v_isExporting_980_; 
v_isExporting_980_ = lean_ctor_get_uint8(v_env_978_, sizeof(void*)*8);
if (v_isExporting_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec_ref(v_env_978_);
lean_dec(v_declHint_974_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_msg_973_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; uint8_t v___x_983_; 
lean_inc_ref(v_env_978_);
v___x_982_ = l_Lean_Environment_setExporting(v_env_978_, v___x_979_);
lean_inc(v_declHint_974_);
lean_inc_ref(v___x_982_);
v___x_983_ = l_Lean_Environment_contains(v___x_982_, v_declHint_974_, v_isExporting_980_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v___x_982_);
lean_dec_ref(v_env_978_);
lean_dec(v_declHint_974_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_msg_973_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_c_990_; lean_object* v___x_991_; 
v___x_985_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__2);
v___x_986_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__6___closed__5);
v___x_987_ = l_Lean_Options_empty;
v___x_988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_988_, 0, v___x_982_);
lean_ctor_set(v___x_988_, 1, v___x_985_);
lean_ctor_set(v___x_988_, 2, v___x_986_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
lean_inc(v_declHint_974_);
v___x_989_ = l_Lean_MessageData_ofConstName(v_declHint_974_, v___x_979_);
v_c_990_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_990_, 0, v___x_988_);
lean_ctor_set(v_c_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_978_, v_declHint_974_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v_env_978_);
lean_dec(v_declHint_974_);
v___x_992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_c_990_);
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_MessageData_note(v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v_msg_973_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1034_; 
v_val_999_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1001_ = v___x_991_;
v_isShared_1002_ = v_isSharedCheck_1034_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v___x_991_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1034_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_mod_1006_; uint8_t v___x_1007_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Lean_Environment_header(v_env_978_);
lean_dec_ref(v_env_978_);
v___x_1005_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1004_);
v_mod_1006_ = lean_array_get(v___x_1003_, v___x_1005_, v_val_999_);
lean_dec(v_val_999_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = l_Lean_isPrivateName(v_declHint_974_);
lean_dec(v_declHint_974_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_c_990_);
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_MessageData_ofName(v_mod_1006_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_note(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_msg_973_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1017_);
v___x_1019_ = v___x_1001_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_c_990_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_ofName(v_mod_1006_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_note(v___x_1028_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_msg_973_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1030_);
v___x_1032_ = v___x_1001_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_env_978_);
lean_dec(v_declHint_974_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_973_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_1036_, lean_object* v_declHint_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1036_, v_declHint_1037_, v___y_1038_);
lean_dec(v___y_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19(lean_object* v_msg_1041_, lean_object* v_declHint_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1056_; 
v___x_1046_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1041_, v_declHint_1042_, v___y_1044_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1051_ = l_Lean_unknownIdentifierMessageTag;
v___x_1052_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1052_);
v___x_1054_ = v___x_1049_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_1057_, lean_object* v_declHint_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19(v_msg_1057_, v_declHint_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg(lean_object* v_ref_1063_, lean_object* v_msg_1064_, lean_object* v_declHint_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; 
v___x_1069_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19(v_msg_1064_, v_declHint_1065_, v___y_1066_, v___y_1067_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg(v_ref_1063_, v_a_1070_, v___y_1066_, v___y_1067_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg___boxed(lean_object* v_ref_1072_, lean_object* v_msg_1073_, lean_object* v_declHint_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg(v_ref_1072_, v_msg_1073_, v_declHint_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec(v_ref_1072_);
return v_res_1078_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__0));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg(lean_object* v_ref_1085_, lean_object* v_constName_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1090_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__1);
v___x_1091_ = 0;
lean_inc(v_constName_1086_);
v___x_1092_ = l_Lean_MessageData_ofConstName(v_constName_1086_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1090_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg(v_ref_1085_, v___x_1095_, v_constName_1086_, v___y_1087_, v___y_1088_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___boxed(lean_object* v_ref_1097_, lean_object* v_constName_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg(v_ref_1097_, v_constName_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec(v_ref_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg(lean_object* v_constName_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; 
v_ref_1107_ = lean_ctor_get(v___y_1104_, 5);
lean_inc(v_ref_1107_);
v___x_1108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg(v_ref_1107_, v_constName_1103_, v___y_1104_, v___y_1105_);
lean_dec(v_ref_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_constName_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg(v_constName_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object* v_constName_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_env_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = lean_st_ref_get(v___y_1116_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_env_1119_);
lean_dec(v___x_1118_);
v___x_1120_ = 0;
lean_inc(v_constName_1114_);
v___x_1121_ = l_Lean_Environment_findConstVal_x3f(v_env_1119_, v_constName_1114_, v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg(v_constName_1114_, v___y_1115_, v___y_1116_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v___y_1115_);
lean_dec(v_constName_1114_);
v_val_1123_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_val_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9___boxed(lean_object* v_constName_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_constName_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_constName_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
lean_inc(v_constName_1136_);
v___x_1140_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_constName_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1152_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_levelParams_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_levelParams_1145_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_levelParams_1145_);
lean_dec(v_a_1141_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__10(v_levelParams_1145_, v___x_1146_);
v___x_1148_ = l_Lean_mkConst(v_constName_1136_, v___x_1147_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1148_);
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_constName_1136_);
v_a_1153_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1140_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1140_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_constName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_constName_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(lean_object* v_stx_1166_, lean_object* v_n_1167_, lean_object* v_expectedType_x3f_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
lean_inc_ref(v___y_1169_);
v___x_1172_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4(v_n_1167_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_stx_1166_);
v___x_1176_ = l_Lean_LocalContext_empty;
v___x_1177_ = 0;
v___x_1178_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1176_);
lean_ctor_set(v___x_1178_, 2, v_expectedType_x3f_1168_);
lean_ctor_set(v___x_1178_, 3, v_a_1173_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*4, v___x_1177_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*4 + 1, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
v___x_1180_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5(v___x_1179_, v___y_1169_, v___y_1170_);
lean_dec_ref(v___y_1169_);
return v___x_1180_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v___y_1169_);
lean_dec(v_expectedType_x3f_1168_);
lean_dec(v_stx_1166_);
v_a_1181_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1172_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1172_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_1189_, lean_object* v_n_1190_, lean_object* v_expectedType_x3f_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_stx_1189_, v_n_1190_, v_expectedType_x3f_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(uint8_t v_x_1199_, lean_object* v_stx_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
lean_inc_ref(v___y_1201_);
v___x_1204_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1258_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1258_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1258_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v_infoState_1210_; uint8_t v_enabled_1211_; lean_object* v___x_1212_; 
v___x_1209_ = lean_st_ref_get(v___y_1202_);
v_infoState_1210_ = lean_ctor_get(v___x_1209_, 7);
lean_inc_ref(v_infoState_1210_);
lean_dec(v___x_1209_);
v_enabled_1211_ = lean_ctor_get_uint8(v_infoState_1210_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1210_);
v___x_1212_ = l_Lean_Syntax_getId(v_a_1205_);
if (v_enabled_1211_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v_a_1205_);
lean_dec_ref(v___y_1201_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1212_);
v___x_1214_ = v___x_1207_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
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
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = l_Lean_Name_getRoot(v___x_1212_);
v___x_1217_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1218_ = lean_name_eq(v___x_1216_, v___x_1217_);
lean_dec(v___x_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1220_; 
lean_dec(v_a_1205_);
lean_dec_ref(v___y_1201_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1212_);
v___x_1220_ = v___x_1207_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1212_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
else
{
lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1222_ = lean_st_ref_get(v___y_1202_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
lean_inc(v___x_1212_);
v___x_1225_ = l_Lean_Name_replacePrefix(v___x_1212_, v___x_1217_, v___x_1224_);
lean_inc(v___x_1225_);
v___x_1226_ = l_Lean_Environment_contains(v_env_1223_, v___x_1225_, v_enabled_1211_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1228_; 
lean_dec(v___x_1225_);
lean_dec(v_a_1205_);
lean_dec_ref(v___y_1201_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1212_);
v___x_1228_ = v___x_1207_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1212_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
uint8_t v___x_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_1207_);
v___x_1230_ = 0;
lean_inc(v___x_1225_);
v___x_1231_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v___x_1225_, v___x_1230_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v___x_1231_);
v___x_1232_ = lean_box(0);
v___x_1233_ = l_Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1(v_a_1205_, v___x_1225_, v___x_1232_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1241_);
v___x_1235_ = v___x_1233_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v___x_1233_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1212_);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1212_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v___x_1212_);
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
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
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___x_1225_);
lean_dec(v___x_1212_);
lean_dec(v_a_1205_);
lean_dec_ref(v___y_1201_);
v_a_1250_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1231_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1231_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
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
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___y_1201_);
v_a_1259_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1204_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1204_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_x_1267_, lean_object* v_stx_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v_x_8592__boxed_1272_; lean_object* v_res_1273_; 
v_x_8592__boxed_1272_ = lean_unbox(v_x_1267_);
v_res_1273_ = l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(v_x_8592__boxed_1272_, v_stx_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1307_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1308_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1306_, v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2____boxed(lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_cls_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_cls_1311_, v___y_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_cls_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_1321_, lean_object* v_m_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___redArg(v_m_1322_, v_a_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_1325_, lean_object* v_m_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_1325_, v_m_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_m_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12(lean_object* v_t_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___redArg(v_t_1329_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12___boxed(lean_object* v_t_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__5_spec__12(v_t_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1340_, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1343_, v_x_1344_, v_x_1345_);
lean_dec_ref(v_x_1345_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1348_, lean_object* v_a_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___redArg(v_a_1349_, v_x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1352_, lean_object* v_a_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_00_u03b2_1352_, v_a_1353_, v_x_1354_);
lean_dec(v_x_1354_);
lean_dec(v_a_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1356_, lean_object* v_x_1357_, size_t v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_1357_, v_x_1358_, v_x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
size_t v_x_8869__boxed_1365_; uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_x_8869__boxed_1365_ = lean_unbox_usize(v_x_1363_);
lean_dec(v_x_1363_);
v_res_1366_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1361_, v_x_1362_, v_x_8869__boxed_1365_, v_x_1364_);
lean_dec_ref(v_x_1364_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12(lean_object* v_00_u03b1_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___redArg(v_constName_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_constName_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12(v_00_u03b1_1374_, v_constName_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1380_, lean_object* v_keys_1381_, lean_object* v_vals_1382_, lean_object* v_heq_1383_, lean_object* v_i_1384_, lean_object* v_k_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_1381_, v_i_1384_, v_k_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_keys_1388_, lean_object* v_vals_1389_, lean_object* v_heq_1390_, lean_object* v_i_1391_, lean_object* v_k_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__10(v_00_u03b2_1387_, v_keys_1388_, v_vals_1389_, v_heq_1390_, v_i_1391_, v_k_1392_);
lean_dec_ref(v_k_1392_);
lean_dec_ref(v_vals_1389_);
lean_dec_ref(v_keys_1388_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16(lean_object* v_00_u03b1_1395_, lean_object* v_ref_1396_, lean_object* v_constName_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg(v_ref_1396_, v_constName_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_constName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16(v_00_u03b1_1402_, v_ref_1403_, v_constName_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec(v_ref_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18(lean_object* v_00_u03b1_1409_, lean_object* v_ref_1410_, lean_object* v_msg_1411_, lean_object* v_declHint_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___redArg(v_ref_1410_, v_msg_1411_, v_declHint_1412_, v___y_1413_, v___y_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_ref_1418_, lean_object* v_msg_1419_, lean_object* v_declHint_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18(v_00_u03b1_1417_, v_ref_1418_, v_msg_1419_, v_declHint_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec(v_ref_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1425_, lean_object* v_declHint_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1425_, v_declHint_1426_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1431_, lean_object* v_declHint_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__19_spec__20(v_msg_1431_, v_declHint_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___redArg(v_ref_1438_, v_msg_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_ref_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20(v_00_u03b1_1444_, v_ref_1445_, v_msg_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec(v_ref_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1452_, v___y_1453_, v___y_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1457_, v_msg_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1466_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1467_ = l_Lean_addBuiltinDocString(v___x_1465_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1497_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1498_ = l_Lean_addBuiltinDeclarationRanges(v___x_1496_, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1529_, uint8_t v___x_1530_, lean_object* v_id_1531_, lean_object* v_x_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1535_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1529_, v___x_1530_);
v___x_1537_ = lean_string_append(v___x_1535_, v___x_1536_);
lean_dec_ref(v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2));
v___x_1539_ = lean_string_append(v___x_1537_, v___x_1538_);
v___x_1540_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1531_, v___x_1539_, v___y_1533_, v___y_1534_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1541_, lean_object* v___x_1542_, lean_object* v_id_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v___x_2591__boxed_1547_; lean_object* v_res_1548_; 
v___x_2591__boxed_1547_ = lean_unbox(v___x_1542_);
v_res_1548_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1541_, v___x_2591__boxed_1547_, v_id_1543_, v_x_1544_, v___y_1545_, v___y_1546_);
lean_dec(v_x_1544_);
lean_dec(v_id_1543_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1559_ = l_String_toRawSubstring_x27(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___y_1567_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1563_);
v___x_1587_ = l_Lean_Syntax_isOfKind(v_x_1563_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_a_1564_);
lean_dec(v_x_1563_);
v___x_1588_ = lean_box(1);
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v_a_1565_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v_id_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = lean_unsigned_to_nat(1u);
v_id_1591_ = l_Lean_Syntax_getArg(v_x_1563_, v___x_1590_);
lean_dec(v_x_1563_);
v___x_1592_ = l_Lean_TSyntax_getId(v_id_1591_);
lean_inc_ref(v_a_1564_);
lean_inc(v___x_1592_);
v___x_1593_ = l_Lean_Macro_resolveGlobalName(v___x_1592_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
if (lean_obj_tag(v_a_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1595_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1593_);
v___x_1596_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1597_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1592_, v___x_1587_);
v___x_1598_ = lean_string_append(v___x_1596_, v___x_1597_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__2));
v___x_1600_ = lean_string_append(v___x_1598_, v___x_1599_);
v___x_1601_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1591_, v___x_1600_, v_a_1564_, v_a_1595_);
lean_dec(v_id_1591_);
v___y_1567_ = v___x_1601_;
goto v___jp_1566_;
}
else
{
lean_object* v_head_1602_; lean_object* v_snd_1603_; 
v_head_1602_ = lean_ctor_get(v_a_1594_, 0);
v_snd_1603_ = lean_ctor_get(v_head_1602_, 1);
if (lean_obj_tag(v_snd_1603_) == 0)
{
lean_object* v_tail_1604_; 
v_tail_1604_ = lean_ctor_get(v_a_1594_, 1);
if (lean_obj_tag(v_tail_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1630_; 
lean_inc(v_head_1602_);
lean_dec_ref(v_a_1594_);
lean_dec(v___x_1592_);
v_a_1605_ = lean_ctor_get(v___x_1593_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1631_);
v___x_1607_ = v___x_1593_;
v_isShared_1608_ = v_isSharedCheck_1630_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1593_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1630_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_fst_1609_; lean_object* v_quotContext_1610_; lean_object* v_currMacroScope_1611_; lean_object* v_ref_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_fst_1609_ = lean_ctor_get(v_head_1602_, 0);
lean_inc(v_fst_1609_);
lean_dec(v_head_1602_);
v_quotContext_1610_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_quotContext_1610_);
v_currMacroScope_1611_ = lean_ctor_get(v_a_1564_, 2);
lean_inc(v_currMacroScope_1611_);
v_ref_1612_ = lean_ctor_get(v_a_1564_, 5);
lean_inc(v_ref_1612_);
lean_dec_ref(v_a_1564_);
v___x_1613_ = 0;
v___x_1614_ = l_Lean_SourceInfo_fromRef(v_ref_1612_, v___x_1613_);
lean_dec(v_ref_1612_);
v___x_1615_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1616_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1617_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1618_ = l_Lean_addMacroScope(v_quotContext_1610_, v___x_1617_, v_currMacroScope_1611_);
v___x_1619_ = lean_box(0);
lean_inc(v___x_1614_);
v___x_1620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1614_);
lean_ctor_set(v___x_1620_, 1, v___x_1616_);
lean_ctor_set(v___x_1620_, 2, v___x_1618_);
lean_ctor_set(v___x_1620_, 3, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
v___x_1622_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1623_ = l_Lean_Name_append(v___x_1622_, v_fst_1609_);
v___x_1624_ = l_Lean_mkIdentFrom(v_id_1591_, v___x_1623_, v___x_1587_);
lean_dec(v_id_1591_);
lean_inc(v___x_1614_);
v___x_1625_ = l_Lean_Syntax_node1(v___x_1614_, v___x_1621_, v___x_1624_);
v___x_1626_ = l_Lean_Syntax_node2(v___x_1614_, v___x_1615_, v___x_1620_, v___x_1625_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1626_);
v___x_1628_ = v___x_1607_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1605_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1593_);
v___x_1633_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1592_, v___x_1587_, v_id_1591_, v_a_1594_, v_a_1564_, v_a_1632_);
lean_dec_ref(v_a_1594_);
lean_dec(v_id_1591_);
v___y_1567_ = v___x_1633_;
goto v___jp_1566_;
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1593_);
v___x_1635_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1592_, v___x_1587_, v_id_1591_, v_a_1594_, v_a_1564_, v_a_1634_);
lean_dec_ref(v_a_1594_);
lean_dec(v_id_1591_);
v___y_1567_ = v___x_1635_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v___x_1592_);
lean_dec(v_id_1591_);
lean_dec_ref(v_a_1564_);
v_a_1636_ = lean_ctor_get(v___x_1593_, 0);
v_a_1637_ = lean_ctor_get(v___x_1593_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1593_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_inc(v_a_1636_);
lean_dec(v___x_1593_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
v___jp_1566_:
{
if (lean_obj_tag(v___y_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1568_ = lean_ctor_get(v___y_1567_, 0);
v_a_1569_ = lean_ctor_get(v___y_1567_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___y_1567_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___y_1567_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_inc(v_a_1568_);
lean_dec(v___y_1567_);
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
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1577_ = lean_ctor_get(v___y_1567_, 0);
v_a_1578_ = lean_ctor_get(v___y_1567_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___y_1567_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___y_1567_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_inc(v_a_1577_);
lean_dec(v___y_1567_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1645_){
_start:
{
lean_object* v_subExpr_1647_; lean_object* v_expr_1648_; lean_object* v___x_1649_; 
v_subExpr_1647_ = lean_ctor_get(v___y_1645_, 3);
v_expr_1648_ = lean_ctor_get(v_subExpr_1647_, 0);
lean_inc_ref(v_expr_1648_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_expr_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1650_);
lean_dec_ref(v___y_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1653_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1669_, lean_object* v_us_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_1672_ = l_Lean_Name_append(v___x_1671_, v_c_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1673_, lean_object* v_us_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1673_, v_us_1674_);
lean_dec(v_us_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1681_);
lean_dec(v_x_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1793_; 
v___x_1717_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1710_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1793_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1793_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
switch(lean_obj_tag(v_a_1718_))
{
case 0:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
lean_dec_ref(v_a_1718_);
v___x_1722_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
case 1:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec_ref(v_a_1718_);
v___x_1726_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1726_);
v___x_1728_ = v___x_1720_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
case 2:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_dec_ref(v_a_1718_);
v___x_1730_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1730_);
v___x_1732_ = v___x_1720_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
case 3:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec_ref(v_a_1718_);
v___x_1734_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1734_);
v___x_1736_ = v___x_1720_;
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
case 4:
{
lean_object* v_declName_1738_; lean_object* v_us_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v_declName_1738_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_declName_1738_);
v_us_1739_ = lean_ctor_get(v_a_1718_, 1);
lean_inc(v_us_1739_);
lean_dec_ref(v_a_1718_);
v___x_1740_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1738_, v_us_1739_);
lean_dec(v_us_1739_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1740_);
v___x_1742_ = v___x_1720_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
case 5:
{
lean_object* v_fn_1744_; lean_object* v___x_1745_; 
v_fn_1744_ = lean_ctor_get(v_a_1718_, 0);
lean_inc_ref(v_fn_1744_);
lean_dec_ref(v_a_1718_);
v___x_1745_ = l_Lean_Expr_getAppFn(v_fn_1744_);
lean_dec_ref(v_fn_1744_);
if (lean_obj_tag(v___x_1745_) == 4)
{
lean_object* v_declName_1746_; lean_object* v_us_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v_declName_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_declName_1746_);
v_us_1747_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_us_1747_);
lean_dec_ref(v___x_1745_);
v___x_1748_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1746_, v_us_1747_);
lean_dec(v_us_1747_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1748_);
v___x_1750_ = v___x_1720_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_dec_ref(v___x_1745_);
v___x_1752_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1752_);
v___x_1754_ = v___x_1720_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
case 6:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec_ref(v_a_1718_);
v___x_1756_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1756_);
v___x_1758_ = v___x_1720_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
case 7:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_dec_ref(v_a_1718_);
v___x_1760_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1760_);
v___x_1762_ = v___x_1720_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
case 8:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec_ref(v_a_1718_);
v___x_1764_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1764_);
v___x_1766_ = v___x_1720_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
case 9:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_dec_ref(v_a_1718_);
v___x_1768_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1768_);
v___x_1770_ = v___x_1720_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
case 10:
{
lean_object* v_data_1772_; 
v_data_1772_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_data_1772_);
lean_dec_ref(v_a_1718_);
if (lean_obj_tag(v_data_1772_) == 1)
{
lean_object* v_tail_1773_; 
v_tail_1773_ = lean_ctor_get(v_data_1772_, 1);
if (lean_obj_tag(v_tail_1773_) == 0)
{
lean_object* v_head_1774_; lean_object* v_fst_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_head_1774_ = lean_ctor_get(v_data_1772_, 0);
lean_inc(v_head_1774_);
lean_dec_ref(v_data_1772_);
v_fst_1775_ = lean_ctor_get(v_head_1774_, 0);
lean_inc(v_fst_1775_);
lean_dec(v_head_1774_);
v___x_1776_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1777_ = l_Lean_Name_append(v___x_1776_, v_fst_1775_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1777_);
v___x_1779_ = v___x_1720_;
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
else
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1772_);
lean_dec_ref(v_data_1772_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1781_);
v___x_1783_ = v___x_1720_;
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
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1772_);
lean_dec(v_data_1772_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1785_);
v___x_1787_ = v___x_1720_;
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
}
default: 
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec_ref(v_a_1718_);
v___x_1789_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1789_);
v___x_1791_ = v___x_1720_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1802_, lean_object* v_k_1803_, lean_object* v_v_1804_){
_start:
{
lean_object* v_map_1805_; uint8_t v_hasTrace_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1819_; 
v_map_1805_ = lean_ctor_get(v_o_1802_, 0);
v_hasTrace_1806_ = lean_ctor_get_uint8(v_o_1802_, sizeof(void*)*1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_o_1802_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1808_ = v_o_1802_;
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_map_1805_);
lean_dec(v_o_1802_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; 
lean_inc(v_k_1803_);
v___x_1810_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1803_, v_v_1804_, v_map_1805_);
if (v_hasTrace_1806_ == 0)
{
lean_object* v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1812_ = l_Lean_Name_isPrefixOf(v___x_1811_, v_k_1803_);
lean_dec(v_k_1803_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1814_ = v___x_1808_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1810_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_ctor_set_uint8(v___x_1814_, sizeof(void*)*1, v___x_1812_);
return v___x_1814_;
}
}
else
{
lean_object* v___x_1817_; 
lean_dec(v_k_1803_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1817_ = v___x_1808_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*1, v_hasTrace_1806_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1820_){
_start:
{
lean_object* v_subExpr_1822_; lean_object* v_pos_1823_; lean_object* v___x_1824_; 
v_subExpr_1822_ = lean_ctor_get(v___y_1820_, 3);
v_pos_1823_ = lean_ctor_get(v_subExpr_1822_, 1);
lean_inc(v_pos_1823_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_pos_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1825_);
lean_dec_ref(v___y_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1828_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0(lean_object* v_x_1844_, lean_object* v_____s_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_fst_1853_; lean_object* v_snd_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_fst_1853_ = lean_ctor_get(v_x_1844_, 0);
lean_inc(v_fst_1853_);
v_snd_1854_ = lean_ctor_get(v_x_1844_, 1);
lean_inc(v_snd_1854_);
lean_dec_ref(v_x_1844_);
v___x_1855_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_____s_1845_, v_fst_1853_, v_snd_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0___boxed(lean_object* v_x_1858_, lean_object* v_____s_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lam__0(v_x_1858_, v_____s_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1868_, lean_object* v_k_1869_){
_start:
{
if (lean_obj_tag(v_t_1868_) == 0)
{
lean_object* v_k_1870_; lean_object* v_v_1871_; lean_object* v_l_1872_; lean_object* v_r_1873_; uint8_t v___x_1874_; 
v_k_1870_ = lean_ctor_get(v_t_1868_, 1);
v_v_1871_ = lean_ctor_get(v_t_1868_, 2);
v_l_1872_ = lean_ctor_get(v_t_1868_, 3);
v_r_1873_ = lean_ctor_get(v_t_1868_, 4);
v___x_1874_ = lean_nat_dec_lt(v_k_1869_, v_k_1870_);
if (v___x_1874_ == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_eq(v_k_1869_, v_k_1870_);
if (v___x_1875_ == 0)
{
v_t_1868_ = v_r_1873_;
goto _start;
}
else
{
lean_object* v___x_1877_; 
lean_inc(v_v_1871_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_v_1871_);
return v___x_1877_;
}
}
else
{
v_t_1868_ = v_l_1872_;
goto _start;
}
}
else
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1880_, lean_object* v_k_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1880_, v_k_1881_);
lean_dec(v_k_1881_);
lean_dec(v_t_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(lean_object* v_f_1883_, lean_object* v_init_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_d_1894_; 
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_k_1897_; lean_object* v_v_1898_; lean_object* v_l_1899_; lean_object* v_r_1900_; lean_object* v___x_1901_; 
v_k_1897_ = lean_ctor_get(v_x_1885_, 1);
v_v_1898_ = lean_ctor_get(v_x_1885_, 2);
v_l_1899_ = lean_ctor_get(v_x_1885_, 3);
v_r_1900_ = lean_ctor_get(v_x_1885_, 4);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc_ref(v_f_1883_);
v___x_1901_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(v_f_1883_, v_init_1884_, v_l_1899_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1901_);
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v_a_1903_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1883_);
v_a_1903_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v_a_1902_);
v_d_1894_ = v_a_1903_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1904_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v_a_1902_);
lean_inc(v_v_1898_);
lean_inc(v_k_1897_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_k_1897_);
lean_ctor_set(v___x_1905_, 1, v_v_1898_);
lean_inc_ref(v_f_1883_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___x_1906_ = lean_apply_9(v_f_1883_, v___x_1905_, v_a_1904_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
if (lean_obj_tag(v_a_1907_) == 0)
{
lean_object* v_a_1908_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1883_);
v_a_1908_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v_a_1907_);
v_d_1894_ = v_a_1908_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v_a_1907_);
v_init_1884_ = v_a_1909_;
v_x_1885_ = v_r_1900_;
goto _start;
}
}
else
{
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1883_);
return v___x_1906_;
}
}
}
else
{
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1883_);
return v___x_1901_;
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_f_1883_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_init_1884_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
v___jp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_d_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg___boxed(lean_object* v_f_1913_, lean_object* v_init_1914_, lean_object* v_x_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(v_f_1913_, v_init_1914_, v_x_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v_x_1915_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_o_1924_, lean_object* v_init_1925_, lean_object* v_f_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_map_1934_; lean_object* v___x_1935_; 
v_map_1934_ = lean_ctor_get(v_o_1924_, 0);
v___x_1935_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(v_f_1926_, v_init_1925_, v_map_1934_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_a_1940_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_a_1940_);
lean_dec(v_a_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_a_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1935_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1935_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_o_1953_, lean_object* v_init_1954_, lean_object* v_f_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_o_1953_, v_init_1954_, v_f_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec_ref(v_o_1953_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_options_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1986_; 
v_options_1972_ = lean_ctor_get(v_a_1969_, 2);
lean_inc_ref(v_options_1972_);
v___x_1973_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1965_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_optionsPerPos_1978_; lean_object* v___x_1979_; 
v_optionsPerPos_1978_ = lean_ctor_get(v_a_1965_, 0);
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1978_, v_a_1974_);
lean_dec(v_a_1974_);
if (lean_obj_tag(v___x_1979_) == 1)
{
lean_object* v_val_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; 
lean_del_object(v___x_1976_);
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v___x_1979_);
v___f_1981_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__0));
v___x_1982_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_val_1980_, v_options_1972_, v___f_1981_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_val_1980_);
return v___x_1982_;
}
else
{
lean_object* v___x_1984_; 
lean_dec(v___x_1979_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_options_1972_);
v___x_1984_ = v___x_1976_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_options_1972_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1995_, lean_object* v_t_1996_, lean_object* v_k_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1996_, v_k_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1999_, lean_object* v_t_2000_, lean_object* v_k_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1999_, v_t_2000_, v_k_2001_);
lean_dec(v_k_2001_);
lean_dec(v_t_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_00_u03b2_2003_, lean_object* v_o_2004_, lean_object* v_init_2005_, lean_object* v_f_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_o_2004_, v_init_2005_, v_f_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_00_u03b2_2015_, lean_object* v_o_2016_, lean_object* v_init_2017_, lean_object* v_f_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_00_u03b2_2015_, v_o_2016_, v_init_2017_, v_f_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec_ref(v_o_2016_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3(lean_object* v_00_u03b2_2027_, lean_object* v_f_2028_, lean_object* v_init_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___redArg(v_f_2028_, v_init_2029_, v_x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_f_2040_, lean_object* v_init_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Options_instForInProdNameDataValueOfMonad___private__1___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3_spec__3(v_00_u03b2_2039_, v_f_2040_, v_init_2041_, v_x_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v_x_2042_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_apply_1(v_opt_2051_, v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_opt_2051_);
v_a_2069_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2059_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2059_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_2086_, lean_object* v_opt_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_2096_, lean_object* v_opt_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_2096_, v_opt_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_2106_, lean_object* v_d_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; 
lean_inc(v_a_2113_);
lean_inc_ref(v_a_2112_);
lean_inc(v_a_2111_);
lean_inc_ref(v_a_2110_);
lean_inc(v_a_2109_);
lean_inc_ref(v_a_2108_);
v___x_2115_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2106_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec_ref(v_d_2107_);
v___x_2118_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_apply_7(v_d_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, lean_box(0));
return v___x_2119_;
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec_ref(v_d_2107_);
v_a_2120_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2115_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2115_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2128_, lean_object* v_d_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2128_, v_d_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2138_, lean_object* v_d_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___x_2147_; 
lean_inc(v_a_2145_);
lean_inc_ref(v_a_2144_);
lean_inc(v_a_2143_);
lean_inc_ref(v_a_2142_);
lean_inc(v_a_2141_);
lean_inc_ref(v_a_2140_);
v___x_2147_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2138_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; uint8_t v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = lean_unbox(v_a_2148_);
lean_dec(v_a_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_apply_7(v_d_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, lean_box(0));
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec_ref(v_d_2139_);
v___x_2151_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2151_;
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec_ref(v_d_2139_);
v_a_2152_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2147_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2147_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2160_, lean_object* v_d_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2160_, v_d_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2170_, lean_object* v_v_2171_, lean_object* v_t_2172_){
_start:
{
if (lean_obj_tag(v_t_2172_) == 0)
{
lean_object* v_size_2173_; lean_object* v_k_2174_; lean_object* v_v_2175_; lean_object* v_l_2176_; lean_object* v_r_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2458_; 
v_size_2173_ = lean_ctor_get(v_t_2172_, 0);
v_k_2174_ = lean_ctor_get(v_t_2172_, 1);
v_v_2175_ = lean_ctor_get(v_t_2172_, 2);
v_l_2176_ = lean_ctor_get(v_t_2172_, 3);
v_r_2177_ = lean_ctor_get(v_t_2172_, 4);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_t_2172_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2179_ = v_t_2172_;
v_isShared_2180_ = v_isSharedCheck_2458_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_r_2177_);
lean_inc(v_l_2176_);
lean_inc(v_v_2175_);
lean_inc(v_k_2174_);
lean_inc(v_size_2173_);
lean_dec(v_t_2172_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2458_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_nat_dec_lt(v_k_2170_, v_k_2174_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_eq(v_k_2170_, v_k_2174_);
if (v___x_2182_ == 0)
{
lean_object* v_impl_2183_; lean_object* v___x_2184_; 
lean_dec(v_size_2173_);
v_impl_2183_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2170_, v_v_2171_, v_r_2177_);
v___x_2184_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2176_) == 0)
{
lean_object* v_size_2185_; lean_object* v_size_2186_; lean_object* v_k_2187_; lean_object* v_v_2188_; lean_object* v_l_2189_; lean_object* v_r_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v_size_2185_ = lean_ctor_get(v_l_2176_, 0);
v_size_2186_ = lean_ctor_get(v_impl_2183_, 0);
lean_inc(v_size_2186_);
v_k_2187_ = lean_ctor_get(v_impl_2183_, 1);
lean_inc(v_k_2187_);
v_v_2188_ = lean_ctor_get(v_impl_2183_, 2);
lean_inc(v_v_2188_);
v_l_2189_ = lean_ctor_get(v_impl_2183_, 3);
lean_inc(v_l_2189_);
v_r_2190_ = lean_ctor_get(v_impl_2183_, 4);
lean_inc(v_r_2190_);
v___x_2191_ = lean_unsigned_to_nat(3u);
v___x_2192_ = lean_nat_mul(v___x_2191_, v_size_2185_);
v___x_2193_ = lean_nat_dec_lt(v___x_2192_, v_size_2186_);
lean_dec(v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_dec(v_r_2190_);
lean_dec(v_l_2189_);
lean_dec(v_v_2188_);
lean_dec(v_k_2187_);
v___x_2194_ = lean_nat_add(v___x_2184_, v_size_2185_);
v___x_2195_ = lean_nat_add(v___x_2194_, v_size_2186_);
lean_dec(v_size_2186_);
lean_dec(v___x_2194_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_impl_2183_);
lean_ctor_set(v___x_2179_, 0, v___x_2195_);
v___x_2197_ = v___x_2179_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_l_2176_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_impl_2183_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
else
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2262_; 
v_isSharedCheck_2262_ = !lean_is_exclusive(v_impl_2183_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; lean_object* v_unused_2264_; lean_object* v_unused_2265_; lean_object* v_unused_2266_; lean_object* v_unused_2267_; 
v_unused_2263_ = lean_ctor_get(v_impl_2183_, 4);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_impl_2183_, 3);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_impl_2183_, 2);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_impl_2183_, 1);
lean_dec(v_unused_2266_);
v_unused_2267_ = lean_ctor_get(v_impl_2183_, 0);
lean_dec(v_unused_2267_);
v___x_2200_ = v_impl_2183_;
v_isShared_2201_ = v_isSharedCheck_2262_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_impl_2183_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2262_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_size_2202_; lean_object* v_k_2203_; lean_object* v_v_2204_; lean_object* v_l_2205_; lean_object* v_r_2206_; lean_object* v_size_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_size_2202_ = lean_ctor_get(v_l_2189_, 0);
v_k_2203_ = lean_ctor_get(v_l_2189_, 1);
v_v_2204_ = lean_ctor_get(v_l_2189_, 2);
v_l_2205_ = lean_ctor_get(v_l_2189_, 3);
v_r_2206_ = lean_ctor_get(v_l_2189_, 4);
v_size_2207_ = lean_ctor_get(v_r_2190_, 0);
v___x_2208_ = lean_unsigned_to_nat(2u);
v___x_2209_ = lean_nat_mul(v___x_2208_, v_size_2207_);
v___x_2210_ = lean_nat_dec_lt(v_size_2202_, v___x_2209_);
lean_dec(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2238_; 
lean_inc(v_r_2206_);
lean_inc(v_l_2205_);
lean_inc(v_v_2204_);
lean_inc(v_k_2203_);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_l_2189_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; lean_object* v_unused_2240_; lean_object* v_unused_2241_; lean_object* v_unused_2242_; lean_object* v_unused_2243_; 
v_unused_2239_ = lean_ctor_get(v_l_2189_, 4);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v_l_2189_, 3);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2189_, 2);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_l_2189_, 1);
lean_dec(v_unused_2242_);
v_unused_2243_ = lean_ctor_get(v_l_2189_, 0);
lean_dec(v_unused_2243_);
v___x_2212_ = v_l_2189_;
v_isShared_2213_ = v_isSharedCheck_2238_;
goto v_resetjp_2211_;
}
else
{
lean_dec(v_l_2189_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2238_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2228_; 
v___x_2214_ = lean_nat_add(v___x_2184_, v_size_2185_);
v___x_2215_ = lean_nat_add(v___x_2214_, v_size_2186_);
lean_dec(v_size_2186_);
if (lean_obj_tag(v_l_2205_) == 0)
{
lean_object* v_size_2236_; 
v_size_2236_ = lean_ctor_get(v_l_2205_, 0);
lean_inc(v_size_2236_);
v___y_2228_ = v_size_2236_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_unsigned_to_nat(0u);
v___y_2228_ = v___x_2237_;
goto v___jp_2227_;
}
v___jp_2216_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_nat_add(v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec(v___y_2218_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 4, v_r_2190_);
lean_ctor_set(v___x_2212_, 3, v_r_2206_);
lean_ctor_set(v___x_2212_, 2, v_v_2188_);
lean_ctor_set(v___x_2212_, 1, v_k_2187_);
lean_ctor_set(v___x_2212_, 0, v___x_2220_);
v___x_2222_ = v___x_2212_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2187_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2188_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_r_2206_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_r_2190_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 4, v___x_2222_);
lean_ctor_set(v___x_2200_, 3, v___y_2217_);
lean_ctor_set(v___x_2200_, 2, v_v_2204_);
lean_ctor_set(v___x_2200_, 1, v_k_2203_);
lean_ctor_set(v___x_2200_, 0, v___x_2215_);
v___x_2224_ = v___x_2200_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v___y_2217_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_nat_add(v___x_2214_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec(v___x_2214_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_l_2205_);
lean_ctor_set(v___x_2179_, 0, v___x_2229_);
v___x_2231_ = v___x_2179_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_l_2176_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_l_2205_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_nat_add(v___x_2184_, v_size_2207_);
if (lean_obj_tag(v_r_2206_) == 0)
{
lean_object* v_size_2233_; 
v_size_2233_ = lean_ctor_get(v_r_2206_, 0);
lean_inc(v_size_2233_);
v___y_2217_ = v___x_2231_;
v___y_2218_ = v___x_2232_;
v___y_2219_ = v_size_2233_;
goto v___jp_2216_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_unsigned_to_nat(0u);
v___y_2217_ = v___x_2231_;
v___y_2218_ = v___x_2232_;
v___y_2219_ = v___x_2234_;
goto v___jp_2216_;
}
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_del_object(v___x_2179_);
v___x_2244_ = lean_nat_add(v___x_2184_, v_size_2185_);
v___x_2245_ = lean_nat_add(v___x_2244_, v_size_2186_);
lean_dec(v_size_2186_);
v___x_2246_ = lean_nat_add(v___x_2244_, v_size_2202_);
lean_dec(v___x_2244_);
lean_inc_ref(v_l_2176_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 4, v_l_2189_);
lean_ctor_set(v___x_2200_, 3, v_l_2176_);
lean_ctor_set(v___x_2200_, 2, v_v_2175_);
lean_ctor_set(v___x_2200_, 1, v_k_2174_);
lean_ctor_set(v___x_2200_, 0, v___x_2246_);
v___x_2248_ = v___x_2200_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_l_2176_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_l_2189_);
v___x_2248_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_isSharedCheck_2255_ = !lean_is_exclusive(v_l_2176_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2256_ = lean_ctor_get(v_l_2176_, 4);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_l_2176_, 3);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_l_2176_, 2);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_l_2176_, 1);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_l_2176_, 0);
lean_dec(v_unused_2260_);
v___x_2250_ = v_l_2176_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v_l_2176_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 4, v_r_2190_);
lean_ctor_set(v___x_2250_, 3, v___x_2248_);
lean_ctor_set(v___x_2250_, 2, v_v_2188_);
lean_ctor_set(v___x_2250_, 1, v_k_2187_);
lean_ctor_set(v___x_2250_, 0, v___x_2245_);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2187_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2188_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2190_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2268_; 
v_l_2268_ = lean_ctor_get(v_impl_2183_, 3);
lean_inc(v_l_2268_);
if (lean_obj_tag(v_l_2268_) == 0)
{
lean_object* v_r_2269_; lean_object* v_k_2270_; lean_object* v_v_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2294_; 
v_r_2269_ = lean_ctor_get(v_impl_2183_, 4);
v_k_2270_ = lean_ctor_get(v_impl_2183_, 1);
v_v_2271_ = lean_ctor_get(v_impl_2183_, 2);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_impl_2183_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2295_ = lean_ctor_get(v_impl_2183_, 3);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2183_, 0);
lean_dec(v_unused_2296_);
v___x_2273_ = v_impl_2183_;
v_isShared_2274_ = v_isSharedCheck_2294_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_r_2269_);
lean_inc(v_v_2271_);
lean_inc(v_k_2270_);
lean_dec(v_impl_2183_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2294_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_k_2275_; lean_object* v_v_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2290_; 
v_k_2275_ = lean_ctor_get(v_l_2268_, 1);
v_v_2276_ = lean_ctor_get(v_l_2268_, 2);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_l_2268_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2291_ = lean_ctor_get(v_l_2268_, 4);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_l_2268_, 3);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_l_2268_, 0);
lean_dec(v_unused_2293_);
v___x_2278_ = v_l_2268_;
v_isShared_2279_ = v_isSharedCheck_2290_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_v_2276_);
lean_inc(v_k_2275_);
lean_dec(v_l_2268_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2290_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2269_, 2);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 4, v_r_2269_);
lean_ctor_set(v___x_2278_, 3, v_r_2269_);
lean_ctor_set(v___x_2278_, 2, v_v_2175_);
lean_ctor_set(v___x_2278_, 1, v_k_2174_);
lean_ctor_set(v___x_2278_, 0, v___x_2184_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v_r_2269_);
lean_ctor_set(v_reuseFailAlloc_2289_, 4, v_r_2269_);
v___x_2282_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
lean_inc(v_r_2269_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 3, v_r_2269_);
lean_ctor_set(v___x_2273_, 0, v___x_2184_);
v___x_2284_ = v___x_2273_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_r_2269_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_r_2269_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2286_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v___x_2284_);
lean_ctor_set(v___x_2179_, 3, v___x_2282_);
lean_ctor_set(v___x_2179_, 2, v_v_2276_);
lean_ctor_set(v___x_2179_, 1, v_k_2275_);
lean_ctor_set(v___x_2179_, 0, v___x_2280_);
v___x_2286_ = v___x_2179_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_k_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_v_2276_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
else
{
lean_object* v_r_2297_; 
v_r_2297_ = lean_ctor_get(v_impl_2183_, 4);
lean_inc(v_r_2297_);
if (lean_obj_tag(v_r_2297_) == 0)
{
lean_object* v_k_2298_; lean_object* v_v_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_k_2298_ = lean_ctor_get(v_impl_2183_, 1);
v_v_2299_ = lean_ctor_get(v_impl_2183_, 2);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_impl_2183_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; 
v_unused_2311_ = lean_ctor_get(v_impl_2183_, 4);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_impl_2183_, 3);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_impl_2183_, 0);
lean_dec(v_unused_2313_);
v___x_2301_ = v_impl_2183_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_v_2299_);
lean_inc(v_k_2298_);
lean_dec(v_impl_2183_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = lean_unsigned_to_nat(3u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_l_2268_);
lean_ctor_set(v___x_2301_, 2, v_v_2175_);
lean_ctor_set(v___x_2301_, 1, v_k_2174_);
lean_ctor_set(v___x_2301_, 0, v___x_2184_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_l_2268_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_l_2268_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_r_2297_);
lean_ctor_set(v___x_2179_, 3, v___x_2305_);
lean_ctor_set(v___x_2179_, 2, v_v_2299_);
lean_ctor_set(v___x_2179_, 1, v_k_2298_);
lean_ctor_set(v___x_2179_, 0, v___x_2303_);
v___x_2307_ = v___x_2179_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2298_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2299_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_r_2297_);
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
else
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(2u);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_impl_2183_);
lean_ctor_set(v___x_2179_, 3, v_r_2297_);
lean_ctor_set(v___x_2179_, 0, v___x_2314_);
v___x_2316_ = v___x_2179_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_r_2297_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_impl_2183_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_object* v___x_2319_; 
lean_dec(v_v_2175_);
lean_dec(v_k_2174_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 2, v_v_2171_);
lean_ctor_set(v___x_2179_, 1, v_k_2170_);
v___x_2319_ = v___x_2179_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_size_2173_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_l_2176_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_r_2177_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_impl_2321_; lean_object* v___x_2322_; 
lean_dec(v_size_2173_);
v_impl_2321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2170_, v_v_2171_, v_l_2176_);
v___x_2322_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2177_) == 0)
{
lean_object* v_size_2323_; lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_size_2323_ = lean_ctor_get(v_r_2177_, 0);
v_size_2324_ = lean_ctor_get(v_impl_2321_, 0);
lean_inc(v_size_2324_);
v_k_2325_ = lean_ctor_get(v_impl_2321_, 1);
lean_inc(v_k_2325_);
v_v_2326_ = lean_ctor_get(v_impl_2321_, 2);
lean_inc(v_v_2326_);
v_l_2327_ = lean_ctor_get(v_impl_2321_, 3);
lean_inc(v_l_2327_);
v_r_2328_ = lean_ctor_get(v_impl_2321_, 4);
lean_inc(v_r_2328_);
v___x_2329_ = lean_unsigned_to_nat(3u);
v___x_2330_ = lean_nat_mul(v___x_2329_, v_size_2323_);
v___x_2331_ = lean_nat_dec_lt(v___x_2330_, v_size_2324_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_dec(v_r_2328_);
lean_dec(v_l_2327_);
lean_dec(v_v_2326_);
lean_dec(v_k_2325_);
v___x_2332_ = lean_nat_add(v___x_2322_, v_size_2324_);
lean_dec(v_size_2324_);
v___x_2333_ = lean_nat_add(v___x_2332_, v_size_2323_);
lean_dec(v___x_2332_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 3, v_impl_2321_);
lean_ctor_set(v___x_2179_, 0, v___x_2333_);
v___x_2335_ = v___x_2179_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_impl_2321_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_r_2177_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
else
{
lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2402_; 
v_isSharedCheck_2402_ = !lean_is_exclusive(v_impl_2321_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2403_ = lean_ctor_get(v_impl_2321_, 4);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_impl_2321_, 3);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_impl_2321_, 2);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_impl_2321_, 1);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_impl_2321_, 0);
lean_dec(v_unused_2407_);
v___x_2338_ = v_impl_2321_;
v_isShared_2339_ = v_isSharedCheck_2402_;
goto v_resetjp_2337_;
}
else
{
lean_dec(v_impl_2321_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2402_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_size_2340_; lean_object* v_size_2341_; lean_object* v_k_2342_; lean_object* v_v_2343_; lean_object* v_l_2344_; lean_object* v_r_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_size_2340_ = lean_ctor_get(v_l_2327_, 0);
v_size_2341_ = lean_ctor_get(v_r_2328_, 0);
v_k_2342_ = lean_ctor_get(v_r_2328_, 1);
v_v_2343_ = lean_ctor_get(v_r_2328_, 2);
v_l_2344_ = lean_ctor_get(v_r_2328_, 3);
v_r_2345_ = lean_ctor_get(v_r_2328_, 4);
v___x_2346_ = lean_unsigned_to_nat(2u);
v___x_2347_ = lean_nat_mul(v___x_2346_, v_size_2340_);
v___x_2348_ = lean_nat_dec_lt(v_size_2341_, v___x_2347_);
lean_dec(v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2377_; 
lean_inc(v_r_2345_);
lean_inc(v_l_2344_);
lean_inc(v_v_2343_);
lean_inc(v_k_2342_);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_r_2328_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; 
v_unused_2378_ = lean_ctor_get(v_r_2328_, 4);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_r_2328_, 3);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_r_2328_, 2);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_r_2328_, 1);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_r_2328_, 0);
lean_dec(v_unused_2382_);
v___x_2350_ = v_r_2328_;
v_isShared_2351_ = v_isSharedCheck_2377_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v_r_2328_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2377_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___x_2365_; lean_object* v___y_2367_; 
v___x_2352_ = lean_nat_add(v___x_2322_, v_size_2324_);
lean_dec(v_size_2324_);
v___x_2353_ = lean_nat_add(v___x_2352_, v_size_2323_);
lean_dec(v___x_2352_);
v___x_2365_ = lean_nat_add(v___x_2322_, v_size_2340_);
if (lean_obj_tag(v_l_2344_) == 0)
{
lean_object* v_size_2375_; 
v_size_2375_ = lean_ctor_get(v_l_2344_, 0);
lean_inc(v_size_2375_);
v___y_2367_ = v_size_2375_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_unsigned_to_nat(0u);
v___y_2367_ = v___x_2376_;
goto v___jp_2366_;
}
v___jp_2354_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_nat_add(v___y_2355_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec(v___y_2355_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_r_2177_);
lean_ctor_set(v___x_2350_, 3, v_r_2345_);
lean_ctor_set(v___x_2350_, 2, v_v_2175_);
lean_ctor_set(v___x_2350_, 1, v_k_2174_);
lean_ctor_set(v___x_2350_, 0, v___x_2358_);
v___x_2360_ = v___x_2350_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_r_2345_);
lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_r_2177_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 4, v___x_2360_);
lean_ctor_set(v___x_2338_, 3, v___y_2356_);
lean_ctor_set(v___x_2338_, 2, v_v_2343_);
lean_ctor_set(v___x_2338_, 1, v_k_2342_);
lean_ctor_set(v___x_2338_, 0, v___x_2353_);
v___x_2362_ = v___x_2338_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_k_2342_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_v_2343_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v___y_2356_);
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
v___jp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_nat_add(v___x_2365_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec(v___x_2365_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_l_2344_);
lean_ctor_set(v___x_2179_, 3, v_l_2327_);
lean_ctor_set(v___x_2179_, 2, v_v_2326_);
lean_ctor_set(v___x_2179_, 1, v_k_2325_);
lean_ctor_set(v___x_2179_, 0, v___x_2368_);
v___x_2370_ = v___x_2179_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_l_2327_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_l_2344_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_nat_add(v___x_2322_, v_size_2323_);
if (lean_obj_tag(v_r_2345_) == 0)
{
lean_object* v_size_2372_; 
v_size_2372_ = lean_ctor_get(v_r_2345_, 0);
lean_inc(v_size_2372_);
v___y_2355_ = v___x_2371_;
v___y_2356_ = v___x_2370_;
v___y_2357_ = v_size_2372_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___y_2355_ = v___x_2371_;
v___y_2356_ = v___x_2370_;
v___y_2357_ = v___x_2373_;
goto v___jp_2354_;
}
}
}
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_del_object(v___x_2179_);
v___x_2383_ = lean_nat_add(v___x_2322_, v_size_2324_);
lean_dec(v_size_2324_);
v___x_2384_ = lean_nat_add(v___x_2383_, v_size_2323_);
lean_dec(v___x_2383_);
v___x_2385_ = lean_nat_add(v___x_2322_, v_size_2323_);
v___x_2386_ = lean_nat_add(v___x_2385_, v_size_2341_);
lean_dec(v___x_2385_);
lean_inc_ref(v_r_2177_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 4, v_r_2177_);
lean_ctor_set(v___x_2338_, 3, v_r_2328_);
lean_ctor_set(v___x_2338_, 2, v_v_2175_);
lean_ctor_set(v___x_2338_, 1, v_k_2174_);
lean_ctor_set(v___x_2338_, 0, v___x_2386_);
v___x_2388_ = v___x_2338_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_r_2328_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_r_2177_);
v___x_2388_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_isSharedCheck_2395_ = !lean_is_exclusive(v_r_2177_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2396_ = lean_ctor_get(v_r_2177_, 4);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_r_2177_, 3);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_r_2177_, 2);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_r_2177_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_r_2177_, 0);
lean_dec(v_unused_2400_);
v___x_2390_ = v_r_2177_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_dec(v_r_2177_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v___x_2388_);
lean_ctor_set(v___x_2390_, 3, v_l_2327_);
lean_ctor_set(v___x_2390_, 2, v_v_2326_);
lean_ctor_set(v___x_2390_, 1, v_k_2325_);
lean_ctor_set(v___x_2390_, 0, v___x_2384_);
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_l_2327_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v___x_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2408_; 
v_l_2408_ = lean_ctor_get(v_impl_2321_, 3);
lean_inc(v_l_2408_);
if (lean_obj_tag(v_l_2408_) == 0)
{
lean_object* v_r_2409_; lean_object* v_k_2410_; lean_object* v_v_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2422_; 
v_r_2409_ = lean_ctor_get(v_impl_2321_, 4);
v_k_2410_ = lean_ctor_get(v_impl_2321_, 1);
v_v_2411_ = lean_ctor_get(v_impl_2321_, 2);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_impl_2321_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2423_ = lean_ctor_get(v_impl_2321_, 3);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_impl_2321_, 0);
lean_dec(v_unused_2424_);
v___x_2413_ = v_impl_2321_;
v_isShared_2414_ = v_isSharedCheck_2422_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_r_2409_);
lean_inc(v_v_2411_);
lean_inc(v_k_2410_);
lean_dec(v_impl_2321_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2422_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2409_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 3, v_r_2409_);
lean_ctor_set(v___x_2413_, 2, v_v_2175_);
lean_ctor_set(v___x_2413_, 1, v_k_2174_);
lean_ctor_set(v___x_2413_, 0, v___x_2322_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_r_2409_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v_r_2409_);
v___x_2417_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v___x_2417_);
lean_ctor_set(v___x_2179_, 3, v_l_2408_);
lean_ctor_set(v___x_2179_, 2, v_v_2411_);
lean_ctor_set(v___x_2179_, 1, v_k_2410_);
lean_ctor_set(v___x_2179_, 0, v___x_2415_);
v___x_2419_ = v___x_2179_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_l_2408_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v_r_2425_; 
v_r_2425_ = lean_ctor_get(v_impl_2321_, 4);
lean_inc(v_r_2425_);
if (lean_obj_tag(v_r_2425_) == 0)
{
lean_object* v_k_2426_; lean_object* v_v_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2450_; 
v_k_2426_ = lean_ctor_get(v_impl_2321_, 1);
v_v_2427_ = lean_ctor_get(v_impl_2321_, 2);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_impl_2321_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; lean_object* v_unused_2452_; lean_object* v_unused_2453_; 
v_unused_2451_ = lean_ctor_get(v_impl_2321_, 4);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_impl_2321_, 3);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v_impl_2321_, 0);
lean_dec(v_unused_2453_);
v___x_2429_ = v_impl_2321_;
v_isShared_2430_ = v_isSharedCheck_2450_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_v_2427_);
lean_inc(v_k_2426_);
lean_dec(v_impl_2321_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2450_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_k_2431_; lean_object* v_v_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2446_; 
v_k_2431_ = lean_ctor_get(v_r_2425_, 1);
v_v_2432_ = lean_ctor_get(v_r_2425_, 2);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_r_2425_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; 
v_unused_2447_ = lean_ctor_get(v_r_2425_, 4);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_r_2425_, 3);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_r_2425_, 0);
lean_dec(v_unused_2449_);
v___x_2434_ = v_r_2425_;
v_isShared_2435_ = v_isSharedCheck_2446_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_v_2432_);
lean_inc(v_k_2431_);
lean_dec(v_r_2425_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2446_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = lean_unsigned_to_nat(3u);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_l_2408_);
lean_ctor_set(v___x_2434_, 3, v_l_2408_);
lean_ctor_set(v___x_2434_, 2, v_v_2427_);
lean_ctor_set(v___x_2434_, 1, v_k_2426_);
lean_ctor_set(v___x_2434_, 0, v___x_2322_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_k_2426_);
lean_ctor_set(v_reuseFailAlloc_2445_, 2, v_v_2427_);
lean_ctor_set(v_reuseFailAlloc_2445_, 3, v_l_2408_);
lean_ctor_set(v_reuseFailAlloc_2445_, 4, v_l_2408_);
v___x_2438_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 4, v_l_2408_);
lean_ctor_set(v___x_2429_, 2, v_v_2175_);
lean_ctor_set(v___x_2429_, 1, v_k_2174_);
lean_ctor_set(v___x_2429_, 0, v___x_2322_);
v___x_2440_ = v___x_2429_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_l_2408_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_l_2408_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2442_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v___x_2440_);
lean_ctor_set(v___x_2179_, 3, v___x_2438_);
lean_ctor_set(v___x_2179_, 2, v_v_2432_);
lean_ctor_set(v___x_2179_, 1, v_k_2431_);
lean_ctor_set(v___x_2179_, 0, v___x_2436_);
v___x_2442_ = v___x_2179_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2431_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2432_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_unsigned_to_nat(2u);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_r_2425_);
lean_ctor_set(v___x_2179_, 3, v_impl_2321_);
lean_ctor_set(v___x_2179_, 0, v___x_2454_);
v___x_2456_ = v___x_2179_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_k_2174_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_v_2175_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_impl_2321_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_r_2425_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v_k_2170_);
lean_ctor_set(v___x_2460_, 2, v_v_2171_);
lean_ctor_set(v___x_2460_, 3, v_t_2172_);
lean_ctor_set(v___x_2460_, 4, v_t_2172_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2461_, lean_object* v_v_2462_, lean_object* v_x_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; lean_object* v_a_2472_; lean_object* v_optionsPerPos_2473_; lean_object* v_currNamespace_2474_; lean_object* v_openDecls_2475_; uint8_t v_inPattern_2476_; lean_object* v_subExpr_2477_; lean_object* v_depth_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2493_; 
v___x_2471_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2464_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v_optionsPerPos_2473_ = lean_ctor_get(v_a_2464_, 0);
v_currNamespace_2474_ = lean_ctor_get(v_a_2464_, 1);
v_openDecls_2475_ = lean_ctor_get(v_a_2464_, 2);
v_inPattern_2476_ = lean_ctor_get_uint8(v_a_2464_, sizeof(void*)*5);
v_subExpr_2477_ = lean_ctor_get(v_a_2464_, 3);
v_depth_2478_ = lean_ctor_get(v_a_2464_, 4);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2480_ = v_a_2464_;
v_isShared_2481_ = v_isSharedCheck_2493_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_depth_2478_);
lean_inc(v_subExpr_2477_);
lean_inc(v_openDecls_2475_);
lean_inc(v_currNamespace_2474_);
lean_inc(v_optionsPerPos_2473_);
lean_dec(v_a_2464_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2493_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___y_2483_; lean_object* v___x_2490_; 
v___x_2490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2473_, v_a_2472_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Options_empty;
v___y_2483_ = v___x_2491_;
goto v___jp_2482_;
}
else
{
lean_object* v_val_2492_; 
v_val_2492_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_val_2492_);
lean_dec_ref(v___x_2490_);
v___y_2483_ = v_val_2492_;
goto v___jp_2482_;
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2483_, v_k_2461_, v_v_2462_);
v___x_2485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2472_, v___x_2484_, v_optionsPerPos_2473_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2485_);
v___x_2487_ = v___x_2480_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_currNamespace_2474_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_openDecls_2475_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_subExpr_2477_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_depth_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2489_, sizeof(void*)*5, v_inPattern_2476_);
v___x_2487_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_apply_7(v_x_2463_, v___x_2487_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2494_, lean_object* v_v_2495_, lean_object* v_x_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2494_, v_v_2495_, v_x_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2505_, lean_object* v_k_2506_, lean_object* v_v_2507_, lean_object* v_x_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2506_, v_v_2507_, v_x_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2517_, lean_object* v_k_2518_, lean_object* v_v_2519_, lean_object* v_x_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2517_, v_k_2518_, v_v_2519_, v_x_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2529_, lean_object* v_k_2530_, lean_object* v_v_2531_, lean_object* v_t_2532_, lean_object* v_hl_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2530_, v_v_2531_, v_t_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2535_, lean_object* v_stx_2536_){
_start:
{
uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = 0;
lean_inc(v_pos_2535_);
v___x_2538_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2538_, 0, v_pos_2535_);
lean_ctor_set(v___x_2538_, 1, v_pos_2535_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*2, v___x_2537_);
v___x_2539_ = l_Lean_Syntax_setInfo(v___x_2538_, v_stx_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2552_; 
v___x_2543_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2541_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2544_, v_stx_2540_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2548_);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2553_, v_a_2554_);
lean_dec_ref(v_a_2554_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2557_, v_a_2558_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2577_, lean_object* v_e_2578_, uint8_t v_isBinder_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_lctx_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_lctx_2582_ = lean_ctor_get(v_a_2580_, 2);
v___x_2583_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_stx_2577_);
v___x_2585_ = lean_box(0);
v___x_2586_ = 0;
lean_inc_ref(v_lctx_2582_);
v___x_2587_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v_lctx_2582_);
lean_ctor_set(v___x_2587_, 2, v___x_2585_);
lean_ctor_set(v___x_2587_, 3, v_e_2578_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*4, v_isBinder_2579_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*4 + 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2589_, lean_object* v_e_2590_, lean_object* v_isBinder_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
uint8_t v_isBinder_boxed_2594_; lean_object* v_res_2595_; 
v_isBinder_boxed_2594_ = lean_unbox(v_isBinder_2591_);
v_res_2595_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2589_, v_e_2590_, v_isBinder_boxed_2594_, v_a_2592_);
lean_dec_ref(v_a_2592_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2596_, lean_object* v_e_2597_, uint8_t v_isBinder_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2596_, v_e_2597_, v_isBinder_2598_, v_a_2601_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2607_, lean_object* v_e_2608_, lean_object* v_isBinder_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
uint8_t v_isBinder_boxed_2617_; lean_object* v_res_2618_; 
v_isBinder_boxed_2617_ = lean_unbox(v_isBinder_2609_);
v_res_2618_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2607_, v_e_2608_, v_isBinder_boxed_2617_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2619_, lean_object* v_stx_2620_, lean_object* v_e_2621_, uint8_t v_isBinder_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2649_; 
v___x_2626_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2620_, v_e_2621_, v_isBinder_2622_, v_a_2624_);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2649_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2649_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v_steps_2632_; lean_object* v_infos_2633_; lean_object* v_holeIter_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2648_; 
v___x_2631_ = lean_st_ref_take(v_a_2623_);
v_steps_2632_ = lean_ctor_get(v___x_2631_, 0);
v_infos_2633_ = lean_ctor_get(v___x_2631_, 1);
v_holeIter_2634_ = lean_ctor_get(v___x_2631_, 2);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2636_ = v___x_2631_;
v_isShared_2637_ = v_isSharedCheck_2648_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_holeIter_2634_);
lean_inc(v_infos_2633_);
lean_inc(v_steps_2632_);
lean_dec(v___x_2631_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2648_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2627_);
v___x_2639_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2619_, v___x_2638_, v_infos_2633_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_steps_2632_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_holeIter_2634_);
v___x_2641_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2642_ = lean_st_ref_set(v_a_2623_, v___x_2641_);
v___x_2643_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2643_);
v___x_2645_ = v___x_2629_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2650_, lean_object* v_stx_2651_, lean_object* v_e_2652_, lean_object* v_isBinder_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
uint8_t v_isBinder_boxed_2657_; lean_object* v_res_2658_; 
v_isBinder_boxed_2657_ = lean_unbox(v_isBinder_2653_);
v_res_2658_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2650_, v_stx_2651_, v_e_2652_, v_isBinder_boxed_2657_, v_a_2654_, v_a_2655_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2659_, lean_object* v_stx_2660_, lean_object* v_e_2661_, uint8_t v_isBinder_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2659_, v_stx_2660_, v_e_2661_, v_isBinder_2662_, v_a_2664_, v_a_2665_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2671_, lean_object* v_stx_2672_, lean_object* v_e_2673_, lean_object* v_isBinder_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
uint8_t v_isBinder_boxed_2682_; lean_object* v_res_2683_; 
v_isBinder_boxed_2682_ = lean_unbox(v_isBinder_2674_);
v_res_2683_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2671_, v_stx_2672_, v_e_2673_, v_isBinder_boxed_2682_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2684_, lean_object* v_fieldName_2685_, lean_object* v_stx_2686_, lean_object* v_val_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_lctx_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_lctx_2690_ = lean_ctor_get(v_a_2688_, 2);
lean_inc_ref(v_lctx_2690_);
v___x_2691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2691_, 0, v_projName_2684_);
lean_ctor_set(v___x_2691_, 1, v_fieldName_2685_);
lean_ctor_set(v___x_2691_, 2, v_lctx_2690_);
lean_ctor_set(v___x_2691_, 3, v_val_2687_);
lean_ctor_set(v___x_2691_, 4, v_stx_2686_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2693_, lean_object* v_fieldName_2694_, lean_object* v_stx_2695_, lean_object* v_val_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2693_, v_fieldName_2694_, v_stx_2695_, v_val_2696_, v_a_2697_);
lean_dec_ref(v_a_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2700_, lean_object* v_fieldName_2701_, lean_object* v_stx_2702_, lean_object* v_val_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2700_, v_fieldName_2701_, v_stx_2702_, v_val_2703_, v_a_2706_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2712_, lean_object* v_fieldName_2713_, lean_object* v_stx_2714_, lean_object* v_val_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2712_, v_fieldName_2713_, v_stx_2714_, v_val_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2724_, lean_object* v_projName_2725_, lean_object* v_fieldName_2726_, lean_object* v_stx_2727_, lean_object* v_val_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2755_; 
v___x_2732_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2725_, v_fieldName_2726_, v_stx_2727_, v_val_2728_, v_a_2730_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2755_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2755_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v_steps_2738_; lean_object* v_infos_2739_; lean_object* v_holeIter_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2754_; 
v___x_2737_ = lean_st_ref_take(v_a_2729_);
v_steps_2738_ = lean_ctor_get(v___x_2737_, 0);
v_infos_2739_ = lean_ctor_get(v___x_2737_, 1);
v_holeIter_2740_ = lean_ctor_get(v___x_2737_, 2);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2742_ = v___x_2737_;
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_holeIter_2740_);
lean_inc(v_infos_2739_);
lean_inc(v_steps_2738_);
lean_dec(v___x_2737_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2744_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_a_2733_);
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2724_, v___x_2744_, v_infos_2739_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2745_);
v___x_2747_ = v___x_2742_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_steps_2738_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_holeIter_2740_);
v___x_2747_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2748_ = lean_st_ref_set(v_a_2729_, v___x_2747_);
v___x_2749_ = lean_box(0);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2749_);
v___x_2751_ = v___x_2735_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2756_, lean_object* v_projName_2757_, lean_object* v_fieldName_2758_, lean_object* v_stx_2759_, lean_object* v_val_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2756_, v_projName_2757_, v_fieldName_2758_, v_stx_2759_, v_val_2760_, v_a_2761_, v_a_2762_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2765_, lean_object* v_projName_2766_, lean_object* v_fieldName_2767_, lean_object* v_stx_2768_, lean_object* v_val_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2765_, v_projName_2766_, v_fieldName_2767_, v_stx_2768_, v_val_2769_, v_a_2771_, v_a_2772_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2778_, lean_object* v_projName_2779_, lean_object* v_fieldName_2780_, lean_object* v_stx_2781_, lean_object* v_val_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2778_, v_projName_2779_, v_fieldName_2780_, v_stx_2781_, v_val_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2791_, lean_object* v_stx_2792_, lean_object* v_e_2793_, uint8_t v_isBinder_2794_, lean_object* v_location_x3f_2795_, lean_object* v_docString_x3f_2796_, uint8_t v_explicit_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2825_; 
v___x_2801_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2792_, v_e_2793_, v_isBinder_2794_, v_a_2799_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2825_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2825_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v_steps_2807_; lean_object* v_infos_2808_; lean_object* v_holeIter_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2824_; 
v___x_2806_ = lean_st_ref_take(v_a_2798_);
v_steps_2807_ = lean_ctor_get(v___x_2806_, 0);
v_infos_2808_ = lean_ctor_get(v___x_2806_, 1);
v_holeIter_2809_ = lean_ctor_get(v___x_2806_, 2);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2811_ = v___x_2806_;
v_isShared_2812_ = v_isSharedCheck_2824_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_holeIter_2809_);
lean_inc(v_infos_2808_);
lean_inc(v_steps_2807_);
lean_dec(v___x_2806_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2824_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2813_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2813_, 0, v_a_2802_);
lean_ctor_set(v___x_2813_, 1, v_location_x3f_2795_);
lean_ctor_set(v___x_2813_, 2, v_docString_x3f_2796_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*3, v_explicit_2797_);
v___x_2814_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
v___x_2815_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2791_, v___x_2814_, v_infos_2808_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 1, v___x_2815_);
v___x_2817_ = v___x_2811_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_steps_2807_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_holeIter_2809_);
v___x_2817_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2818_ = lean_st_ref_set(v_a_2798_, v___x_2817_);
v___x_2819_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2819_);
v___x_2821_ = v___x_2804_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2826_, lean_object* v_stx_2827_, lean_object* v_e_2828_, lean_object* v_isBinder_2829_, lean_object* v_location_x3f_2830_, lean_object* v_docString_x3f_2831_, lean_object* v_explicit_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
uint8_t v_isBinder_boxed_2836_; uint8_t v_explicit_boxed_2837_; lean_object* v_res_2838_; 
v_isBinder_boxed_2836_ = lean_unbox(v_isBinder_2829_);
v_explicit_boxed_2837_ = lean_unbox(v_explicit_2832_);
v_res_2838_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2826_, v_stx_2827_, v_e_2828_, v_isBinder_boxed_2836_, v_location_x3f_2830_, v_docString_x3f_2831_, v_explicit_boxed_2837_, v_a_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2839_, lean_object* v_stx_2840_, lean_object* v_e_2841_, uint8_t v_isBinder_2842_, lean_object* v_location_x3f_2843_, lean_object* v_docString_x3f_2844_, uint8_t v_explicit_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2839_, v_stx_2840_, v_e_2841_, v_isBinder_2842_, v_location_x3f_2843_, v_docString_x3f_2844_, v_explicit_2845_, v_a_2847_, v_a_2848_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2854_, lean_object* v_stx_2855_, lean_object* v_e_2856_, lean_object* v_isBinder_2857_, lean_object* v_location_x3f_2858_, lean_object* v_docString_x3f_2859_, lean_object* v_explicit_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
uint8_t v_isBinder_boxed_2868_; uint8_t v_explicit_boxed_2869_; lean_object* v_res_2870_; 
v_isBinder_boxed_2868_ = lean_unbox(v_isBinder_2857_);
v_explicit_boxed_2869_ = lean_unbox(v_explicit_2860_);
v_res_2870_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2854_, v_stx_2855_, v_e_2856_, v_isBinder_boxed_2868_, v_location_x3f_2858_, v_docString_x3f_2859_, v_explicit_boxed_2869_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2871_, v_a_2872_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v_a_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
v___x_2878_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2872_);
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2872_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = 0;
lean_inc(v_a_2877_);
v___x_2883_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2879_, v_a_2877_, v_a_2881_, v___x_2882_, v_a_2873_, v_a_2874_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v___x_2883_, 0);
lean_dec(v_unused_2891_);
v___x_2885_ = v___x_2883_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v___x_2883_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v_a_2877_);
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2877_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_a_2877_);
v_a_2892_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2883_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2883_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2923_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2924_, lean_object* v_t_2925_){
_start:
{
if (lean_obj_tag(v_t_2925_) == 0)
{
lean_object* v_k_2926_; lean_object* v_l_2927_; lean_object* v_r_2928_; uint8_t v___x_2929_; 
v_k_2926_ = lean_ctor_get(v_t_2925_, 1);
v_l_2927_ = lean_ctor_get(v_t_2925_, 3);
v_r_2928_ = lean_ctor_get(v_t_2925_, 4);
v___x_2929_ = lean_nat_dec_lt(v_k_2924_, v_k_2926_);
if (v___x_2929_ == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_nat_dec_eq(v_k_2924_, v_k_2926_);
if (v___x_2930_ == 0)
{
v_t_2925_ = v_r_2928_;
goto _start;
}
else
{
return v___x_2930_;
}
}
else
{
v_t_2925_ = v_l_2927_;
goto _start;
}
}
else
{
uint8_t v___x_2933_; 
v___x_2933_ = 0;
return v___x_2933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2934_, lean_object* v_t_2935_){
_start:
{
uint8_t v_res_2936_; lean_object* v_r_2937_; 
v_res_2936_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2934_, v_t_2935_);
lean_dec(v_t_2935_);
lean_dec(v_k_2934_);
v_r_2937_ = lean_box(v_res_2936_);
return v_r_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_Syntax_getInfo_x3f(v_stx_2938_);
if (lean_obj_tag(v___x_2943_) == 1)
{
lean_object* v_val_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2963_; 
v_val_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_val_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
if (lean_obj_tag(v_val_2944_) == 1)
{
uint8_t v_canonical_2948_; 
v_canonical_2948_ = lean_ctor_get_uint8(v_val_2944_, sizeof(void*)*2);
if (v_canonical_2948_ == 0)
{
lean_object* v_pos_2949_; lean_object* v_endPos_2950_; lean_object* v___x_2951_; uint8_t v___y_2953_; uint8_t v___x_2958_; 
v_pos_2949_ = lean_ctor_get(v_val_2944_, 0);
lean_inc(v_pos_2949_);
v_endPos_2950_ = lean_ctor_get(v_val_2944_, 1);
lean_inc(v_endPos_2950_);
lean_dec_ref(v_val_2944_);
v___x_2951_ = lean_st_ref_get(v_a_2940_);
v___x_2958_ = lean_nat_dec_eq(v_pos_2949_, v_endPos_2950_);
lean_dec(v_endPos_2950_);
if (v___x_2958_ == 0)
{
lean_dec(v___x_2951_);
lean_dec(v_pos_2949_);
v___y_2953_ = v___x_2958_;
goto v___jp_2952_;
}
else
{
lean_object* v_infos_2959_; uint8_t v___x_2960_; 
v_infos_2959_ = lean_ctor_get(v___x_2951_, 1);
lean_inc(v_infos_2959_);
lean_dec(v___x_2951_);
v___x_2960_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2949_, v_infos_2959_);
lean_dec(v_infos_2959_);
lean_dec(v_pos_2949_);
v___y_2953_ = v___x_2960_;
goto v___jp_2952_;
}
v___jp_2952_:
{
if (v___y_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_del_object(v___x_2946_);
v___x_2954_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
return v___x_2954_;
}
else
{
lean_object* v___x_2956_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 0);
lean_ctor_set(v___x_2946_, 0, v_stx_2938_);
v___x_2956_ = v___x_2946_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_stx_2938_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v___x_2961_; 
lean_dec_ref(v_val_2944_);
lean_del_object(v___x_2946_);
v___x_2961_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
return v___x_2961_;
}
}
else
{
lean_object* v___x_2962_; 
lean_del_object(v___x_2946_);
lean_dec(v_val_2944_);
v___x_2962_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
return v___x_2962_;
}
}
}
else
{
lean_object* v___x_2964_; 
lean_dec(v___x_2943_);
v___x_2964_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
return v_res_2988_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2989_, lean_object* v_k_2990_, lean_object* v_t_2991_){
_start:
{
uint8_t v___x_2992_; 
v___x_2992_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2990_, v_t_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2993_, lean_object* v_k_2994_, lean_object* v_t_2995_){
_start:
{
uint8_t v_res_2996_; lean_object* v_r_2997_; 
v_res_2996_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2993_, v_k_2994_, v_t_2995_);
lean_dec(v_t_2995_);
lean_dec(v_k_2994_);
v_r_2997_ = lean_box(v_res_2996_);
return v_r_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; 
lean_inc_ref(v_a_3001_);
lean_inc(v_a_3000_);
lean_inc_ref(v_a_2999_);
v___x_3006_ = lean_apply_7(v_d_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, lean_box(0));
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_3007_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v___x_3008_;
}
else
{
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v___x_3026_; 
lean_inc_ref(v_a_3021_);
lean_inc(v_a_3020_);
lean_inc_ref(v_a_3019_);
v___x_3026_ = lean_apply_7(v_d_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, lean_box(0));
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3027_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
return v___x_3028_;
}
else
{
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_3038_, lean_object* v_suggestion_x27_3039_, lean_object* v_x_3040_){
_start:
{
if (lean_obj_tag(v_x_3040_) == 1)
{
lean_object* v_fvarId_3041_; lean_object* v___x_3042_; 
v_fvarId_3041_ = lean_ctor_get(v_x_3040_, 0);
lean_inc(v_fvarId_3041_);
lean_dec_ref(v_x_3040_);
v___x_3042_ = lean_local_ctx_find(v_lctx_3038_, v_fvarId_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
uint8_t v___x_3043_; 
v___x_3043_ = 0;
return v___x_3043_;
}
else
{
lean_object* v_val_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v_val_3044_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_val_3044_);
lean_dec_ref(v___x_3042_);
v___x_3045_ = l_Lean_LocalDecl_userName(v_val_3044_);
lean_dec(v_val_3044_);
v___x_3046_ = lean_name_eq(v___x_3045_, v_suggestion_x27_3039_);
lean_dec(v___x_3045_);
return v___x_3046_;
}
}
else
{
uint8_t v___x_3047_; 
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_lctx_3038_);
v___x_3047_ = 0;
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_3048_, lean_object* v_suggestion_x27_3049_, lean_object* v_x_3050_){
_start:
{
uint8_t v_res_3051_; lean_object* v_r_3052_; 
v_res_3051_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_3048_, v_suggestion_x27_3049_, v_x_3050_);
lean_dec(v_suggestion_x27_3049_);
v_r_3052_ = lean_box(v_res_3051_);
return v_r_3052_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_3053_, lean_object* v_lctx_3054_, lean_object* v_suggestion_x27_3055_){
_start:
{
lean_object* v___f_3056_; lean_object* v___x_3057_; 
v___f_3056_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3056_, 0, v_lctx_3054_);
lean_closure_set(v___f_3056_, 1, v_suggestion_x27_3055_);
v___x_3057_ = lean_find_expr(v___f_3056_, v_body_3053_);
lean_dec_ref(v___f_3056_);
if (lean_obj_tag(v___x_3057_) == 0)
{
uint8_t v___x_3058_; 
v___x_3058_ = 0;
return v___x_3058_;
}
else
{
uint8_t v___x_3059_; 
lean_dec_ref(v___x_3057_);
v___x_3059_ = 1;
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_3060_, lean_object* v_lctx_3061_, lean_object* v_suggestion_x27_3062_){
_start:
{
uint8_t v_res_3063_; lean_object* v_r_3064_; 
v_res_3063_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_3060_, v_lctx_3061_, v_suggestion_x27_3062_);
lean_dec_ref(v_body_3060_);
v_r_3064_ = lean_box(v_res_3063_);
return v_r_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_quotContext_3069_; lean_object* v_currMacroScope_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_quotContext_3069_ = lean_ctor_get(v___y_3066_, 10);
lean_inc(v_quotContext_3069_);
v_currMacroScope_3070_ = lean_ctor_get(v___y_3066_, 11);
lean_inc(v_currMacroScope_3070_);
lean_dec_ref(v___y_3066_);
v___x_3071_ = l_Lean_addMacroScope(v_quotContext_3069_, v_snd_3065_, v_currMacroScope_3070_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_3082_, lean_object* v_body_3083_, uint8_t v_preserveName_3084_, lean_object* v_avoid_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v_fst_3125_; lean_object* v_snd_3126_; uint8_t v___x_3132_; 
v___x_3132_ = l_Lean_Name_isAnonymous(v_suggestion_3082_);
if (v___x_3132_ == 0)
{
uint8_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = l_Lean_Name_hasMacroScopes(v_suggestion_3082_);
v___x_3134_ = lean_erase_macro_scopes(v_suggestion_3082_);
v_fst_3125_ = v___x_3133_;
v_snd_3126_ = v___x_3134_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3135_; 
lean_dec(v_suggestion_3082_);
v___x_3135_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3125_ = v___x_3132_;
v_snd_3126_ = v___x_3135_;
goto v___jp_3124_;
}
v___jp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = l_Lean_LocalContext_getUnusedName(v___y_3094_, v___y_3095_);
lean_dec_ref(v___y_3094_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
v___jp_3098_:
{
if (v_preserveName_3084_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref(v___y_3099_);
v___x_3102_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3103_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3102_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3114_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3114_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3114_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3108_ == 0)
{
lean_del_object(v___x_3106_);
v___y_3094_ = v___y_3100_;
v___y_3095_ = v___y_3101_;
goto v___jp_3093_;
}
else
{
uint8_t v___x_3109_; 
v___x_3109_ = l_Lean_NameSet_contains(v_avoid_3085_, v___y_3101_);
if (v___x_3109_ == 0)
{
uint8_t v___x_3110_; 
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
v___x_3110_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_3083_, v___y_3100_, v___y_3101_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3112_; 
lean_dec_ref(v___y_3100_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___y_3101_);
v___x_3112_ = v___x_3106_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___y_3101_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
else
{
lean_del_object(v___x_3106_);
v___y_3094_ = v___y_3100_;
v___y_3095_ = v___y_3101_;
goto v___jp_3093_;
}
}
else
{
lean_del_object(v___x_3106_);
v___y_3094_ = v___y_3100_;
v___y_3095_ = v___y_3101_;
goto v___jp_3093_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
v_a_3115_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3103_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3103_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v___x_3123_; 
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
v___x_3123_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3099_, v_a_3090_, v_a_3091_);
return v___x_3123_;
}
}
v___jp_3124_:
{
lean_object* v_lctx_3127_; uint8_t v___x_3128_; 
v_lctx_3127_ = lean_ctor_get(v_a_3088_, 2);
v___x_3128_ = l_Lean_LocalContext_usesUserName(v_lctx_3127_, v_snd_3126_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_snd_3126_);
return v___x_3129_;
}
else
{
lean_object* v___f_3130_; 
lean_inc(v_snd_3126_);
v___f_3130_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3130_, 0, v_snd_3126_);
if (v_preserveName_3084_ == 0)
{
lean_inc_ref(v_lctx_3127_);
v___y_3099_ = v___f_3130_;
v___y_3100_ = v_lctx_3127_;
v___y_3101_ = v_snd_3126_;
goto v___jp_3098_;
}
else
{
if (v_fst_3125_ == 0)
{
lean_object* v___x_3131_; 
lean_dec_ref(v___f_3130_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_snd_3126_);
return v___x_3131_;
}
else
{
lean_inc_ref(v_lctx_3127_);
v___y_3099_ = v___f_3130_;
v___y_3100_ = v_lctx_3127_;
v___y_3101_ = v_snd_3126_;
goto v___jp_3098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3136_, lean_object* v_body_3137_, lean_object* v_preserveName_3138_, lean_object* v_avoid_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
uint8_t v_preserveName_boxed_3147_; lean_object* v_res_3148_; 
v_preserveName_boxed_3147_ = lean_unbox(v_preserveName_3138_);
v_res_3148_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3136_, v_body_3137_, v_preserveName_boxed_3147_, v_avoid_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
lean_dec(v_avoid_3139_);
lean_dec_ref(v_body_3137_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; lean_object* v_holeIter_3152_; lean_object* v_curr_3153_; lean_object* v___x_3154_; lean_object* v_steps_3155_; lean_object* v_infos_3156_; lean_object* v_holeIter_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3167_; 
v___x_3151_ = lean_st_ref_get(v___y_3149_);
v_holeIter_3152_ = lean_ctor_get(v___x_3151_, 2);
lean_inc_ref(v_holeIter_3152_);
lean_dec(v___x_3151_);
v_curr_3153_ = lean_ctor_get(v_holeIter_3152_, 0);
lean_inc(v_curr_3153_);
lean_dec_ref(v_holeIter_3152_);
v___x_3154_ = lean_st_ref_take(v___y_3149_);
v_steps_3155_ = lean_ctor_get(v___x_3154_, 0);
v_infos_3156_ = lean_ctor_get(v___x_3154_, 1);
v_holeIter_3157_ = lean_ctor_get(v___x_3154_, 2);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3159_ = v___x_3154_;
v_isShared_3160_ = v_isSharedCheck_3167_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_holeIter_3157_);
lean_inc(v_infos_3156_);
lean_inc(v_steps_3155_);
lean_dec(v___x_3154_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3167_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3161_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3157_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 2, v___x_3161_);
v___x_3163_ = v___x_3159_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_steps_3155_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_infos_3156_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_st_ref_set(v___y_3149_, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_curr_3153_);
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3168_);
lean_dec(v___y_3168_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3172_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3187_, lean_object* v_e_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; 
v___x_3196_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3190_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = lean_mk_syntax_ident(v_n_3187_);
lean_inc(v_a_3197_);
v___x_3199_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3197_, v___x_3198_);
v___x_3200_ = 0;
lean_inc(v___x_3199_);
v___x_3201_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3197_, v___x_3199_, v_e_3188_, v___x_3200_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v___x_3201_, 0);
lean_dec(v_unused_3209_);
v___x_3203_ = v___x_3201_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v___x_3201_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3199_);
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3199_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v___x_3199_);
v_a_3210_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3201_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3201_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3218_, lean_object* v_e_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3218_, v_e_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3228_, lean_object* v_x_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_apply_8(v_d_3228_, v_x_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, lean_box(0));
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3238_, v_x_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v_b_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_apply_8(v_k_3248_, v_b_3251_, v___y_3249_, v___y_3250_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, lean_box(0));
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3258_, v___y_3259_, v___y_3260_, v_b_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3268_, uint8_t v_bi_3269_, lean_object* v_type_3270_, lean_object* v_k_3271_, uint8_t v_kind_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___f_3280_; lean_object* v___x_3281_; 
v___f_3280_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3280_, 0, v_k_3271_);
lean_closure_set(v___f_3280_, 1, v___y_3273_);
lean_closure_set(v___f_3280_, 2, v___y_3274_);
v___x_3281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3268_, v_bi_3269_, v_type_3270_, v___f_3280_, v_kind_3272_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3281_) == 0)
{
return v___x_3281_;
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3290_, lean_object* v_bi_3291_, lean_object* v_type_3292_, lean_object* v_k_3293_, lean_object* v_kind_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v_bi_boxed_3302_; uint8_t v_kind_boxed_3303_; lean_object* v_res_3304_; 
v_bi_boxed_3302_ = lean_unbox(v_bi_3291_);
v_kind_boxed_3303_ = lean_unbox(v_kind_3294_);
v_res_3304_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3290_, v_bi_boxed_3302_, v_type_3292_, v_k_3293_, v_kind_boxed_3303_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3305_, lean_object* v_childIdx_3306_, lean_object* v_x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_subExpr_3315_; lean_object* v_optionsPerPos_3316_; lean_object* v_currNamespace_3317_; lean_object* v_openDecls_3318_; uint8_t v_inPattern_3319_; lean_object* v_depth_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3338_; 
v_subExpr_3315_ = lean_ctor_get(v___y_3308_, 3);
v_optionsPerPos_3316_ = lean_ctor_get(v___y_3308_, 0);
v_currNamespace_3317_ = lean_ctor_get(v___y_3308_, 1);
v_openDecls_3318_ = lean_ctor_get(v___y_3308_, 2);
v_inPattern_3319_ = lean_ctor_get_uint8(v___y_3308_, sizeof(void*)*5);
v_depth_3320_ = lean_ctor_get(v___y_3308_, 4);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___y_3308_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3322_ = v___y_3308_;
v_isShared_3323_ = v_isSharedCheck_3338_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_depth_3320_);
lean_inc(v_subExpr_3315_);
lean_inc(v_openDecls_3318_);
lean_inc(v_currNamespace_3317_);
lean_inc(v_optionsPerPos_3316_);
lean_dec(v___y_3308_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3338_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_pos_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3336_; 
v_pos_3324_ = lean_ctor_get(v_subExpr_3315_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_subExpr_3315_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_subExpr_3315_, 0);
lean_dec(v_unused_3337_);
v___x_3326_ = v_subExpr_3315_;
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_pos_3324_);
lean_dec(v_subExpr_3315_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3328_ = l_Lean_SubExpr_Pos_push(v_pos_3324_, v_childIdx_3306_);
lean_dec(v_pos_3324_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 1, v___x_3328_);
lean_ctor_set(v___x_3326_, 0, v_child_3305_);
v___x_3330_ = v___x_3326_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_child_3305_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 3, v___x_3330_);
v___x_3332_ = v___x_3322_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_optionsPerPos_3316_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_currNamespace_3317_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_openDecls_3318_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_depth_3320_);
lean_ctor_set_uint8(v_reuseFailAlloc_3334_, sizeof(void*)*5, v_inPattern_3319_);
v___x_3332_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_apply_7(v_x_3307_, v___x_3332_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, lean_box(0));
return v___x_3333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3339_, lean_object* v_childIdx_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3339_, v_childIdx_3340_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3350_, lean_object* v_a_3351_, lean_object* v_x_3352_, lean_object* v_fvar_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v___y_3355_);
lean_inc_ref(v___y_3354_);
lean_inc_ref(v_fvar_3353_);
v___x_3361_ = lean_apply_8(v_v_3350_, v_fvar_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, lean_box(0));
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_Expr_bindingBody_x21(v_a_3351_);
v___x_3364_ = lean_expr_instantiate1(v___x_3363_, v_fvar_3353_);
lean_dec_ref(v_fvar_3353_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_apply_1(v_x_3352_, v_a_3362_);
v___x_3367_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3364_, v___x_3365_, v___x_3366_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
return v___x_3367_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_fvar_3353_);
lean_dec_ref(v_x_3352_);
v_a_3368_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3361_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3361_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3376_, lean_object* v_a_3377_, lean_object* v_x_3378_, lean_object* v_fvar_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3376_, v_a_3377_, v_x_3378_, v_fvar_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec_ref(v_a_3377_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3388_, lean_object* v_v_3389_, lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___f_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3398_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3391_);
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
lean_inc(v_a_3399_);
v___f_3400_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3400_, 0, v_v_3389_);
lean_closure_set(v___f_3400_, 1, v_a_3399_);
lean_closure_set(v___f_3400_, 2, v_x_3390_);
v___x_3401_ = l_Lean_Expr_binderInfo(v_a_3399_);
v___x_3402_ = l_Lean_Expr_bindingDomain_x21(v_a_3399_);
lean_dec(v_a_3399_);
v___x_3403_ = 0;
v___x_3404_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3388_, v___x_3401_, v___x_3402_, v___f_3400_, v___x_3403_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3405_, lean_object* v_v_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3405_, v_v_3406_, v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3416_, uint8_t v_preserveName_3417_, lean_object* v_avoid_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3426_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3419_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3419_);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = l_Lean_Expr_bindingName_x21(v_a_3427_);
lean_dec(v_a_3427_);
v___x_3431_ = l_Lean_Expr_bindingBody_x21(v_a_3429_);
lean_dec(v_a_3429_);
lean_inc(v_a_3424_);
lean_inc_ref(v_a_3423_);
lean_inc(v_a_3422_);
lean_inc_ref(v_a_3421_);
lean_inc(v_a_3420_);
lean_inc_ref(v_a_3419_);
v___x_3432_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3430_, v___x_3431_, v_preserveName_3417_, v_avoid_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
lean_dec_ref(v___x_3431_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref(v___x_3432_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3434_, 0, v_d_3416_);
lean_inc(v_a_3433_);
v___x_3435_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3435_, 0, v_a_3433_);
v___x_3436_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3433_, v___x_3435_, v___f_3434_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
return v___x_3436_;
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec_ref(v_d_3416_);
v_a_3437_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3432_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3432_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3445_, lean_object* v_preserveName_3446_, lean_object* v_avoid_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
uint8_t v_preserveName_boxed_3455_; lean_object* v_res_3456_; 
v_preserveName_boxed_3455_ = lean_unbox(v_preserveName_3446_);
v_res_3456_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3445_, v_preserveName_boxed_3455_, v_avoid_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
lean_dec(v_avoid_3447_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3457_, lean_object* v_d_3458_, uint8_t v_preserveName_3459_, lean_object* v_avoid_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3458_, v_preserveName_3459_, v_avoid_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3469_, lean_object* v_d_3470_, lean_object* v_preserveName_3471_, lean_object* v_avoid_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
uint8_t v_preserveName_boxed_3480_; lean_object* v_res_3481_; 
v_preserveName_boxed_3480_ = lean_unbox(v_preserveName_3471_);
v_res_3481_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3469_, v_d_3470_, v_preserveName_boxed_3480_, v_avoid_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
lean_dec(v_avoid_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3482_, lean_object* v_child_3483_, lean_object* v_childIdx_3484_, lean_object* v_x_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3483_, v_childIdx_3484_, v_x_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_child_3495_, lean_object* v_childIdx_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3494_, v_child_3495_, v_childIdx_3496_, v_x_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3506_, lean_object* v_name_3507_, uint8_t v_bi_3508_, lean_object* v_type_3509_, lean_object* v_k_3510_, uint8_t v_kind_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3507_, v_bi_3508_, v_type_3509_, v_k_3510_, v_kind_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3520_, lean_object* v_name_3521_, lean_object* v_bi_3522_, lean_object* v_type_3523_, lean_object* v_k_3524_, lean_object* v_kind_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
uint8_t v_bi_boxed_3533_; uint8_t v_kind_boxed_3534_; lean_object* v_res_3535_; 
v_bi_boxed_3533_ = lean_unbox(v_bi_3522_);
v_kind_boxed_3534_ = lean_unbox(v_kind_3525_);
v_res_3535_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3520_, v_name_3521_, v_bi_boxed_3533_, v_type_3523_, v_k_3524_, v_kind_boxed_3534_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3536_, lean_object* v_00_u03b2_3537_, lean_object* v_n_3538_, lean_object* v_v_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3538_, v_v_3539_, v_x_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_00_u03b2_3550_, lean_object* v_n_3551_, lean_object* v_v_3552_, lean_object* v_x_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3549_, v_00_u03b2_3550_, v_n_3551_, v_v_3552_, v_x_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object* v_x_3562_){
_start:
{
switch(lean_obj_tag(v_x_3562_))
{
case 0:
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_unsigned_to_nat(0u);
return v___x_3563_;
}
case 1:
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_unsigned_to_nat(1u);
return v___x_3564_;
}
case 2:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_unsigned_to_nat(2u);
return v___x_3565_;
}
default: 
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_unsigned_to_nat(3u);
return v___x_3566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object* v_x_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(v_x_3567_);
lean_dec(v_x_3567_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3569_, lean_object* v_k_3570_){
_start:
{
if (lean_obj_tag(v_t_3569_) == 3)
{
lean_object* v_s_3571_; lean_object* v___x_3572_; 
v_s_3571_ = lean_ctor_get(v_t_3569_, 0);
lean_inc_ref(v_s_3571_);
lean_dec_ref(v_t_3569_);
v___x_3572_ = lean_apply_1(v_k_3570_, v_s_3571_);
return v___x_3572_;
}
else
{
lean_dec(v_t_3569_);
return v_k_3570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3573_, lean_object* v_ctorIdx_3574_, lean_object* v_t_3575_, lean_object* v_h_3576_, lean_object* v_k_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3575_, v_k_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3579_, lean_object* v_ctorIdx_3580_, lean_object* v_t_3581_, lean_object* v_h_3582_, lean_object* v_k_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3579_, v_ctorIdx_3580_, v_t_3581_, v_h_3582_, v_k_3583_);
lean_dec(v_ctorIdx_3580_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3585_, lean_object* v_deep_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3585_, v_deep_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3588_, lean_object* v_t_3589_, lean_object* v_h_3590_, lean_object* v_deep_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3589_, v_deep_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3593_, lean_object* v_proof_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3593_, v_proof_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3596_, lean_object* v_t_3597_, lean_object* v_h_3598_, lean_object* v_proof_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3597_, v_proof_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3601_, lean_object* v_maxSteps_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3601_, v_maxSteps_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3604_, lean_object* v_t_3605_, lean_object* v_h_3606_, lean_object* v_maxSteps_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3605_, v_maxSteps_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3609_, lean_object* v_string_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3609_, v_string_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3612_, lean_object* v_t_3613_, lean_object* v_h_3614_, lean_object* v_string_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3613_, v_string_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3620_){
_start:
{
switch(lean_obj_tag(v_x_3620_))
{
case 0:
{
lean_object* v___x_3621_; 
v___x_3621_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3621_;
}
case 1:
{
lean_object* v___x_3622_; 
v___x_3622_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3622_;
}
case 2:
{
lean_object* v___x_3623_; 
v___x_3623_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3623_;
}
default: 
{
lean_object* v_s_3624_; 
v_s_3624_ = lean_ctor_get(v_x_3620_, 0);
lean_inc_ref(v_s_3624_);
return v_s_3624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3625_);
lean_dec(v_x_3625_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3627_, lean_object* v_stx_3628_, lean_object* v_e_3629_, lean_object* v_reason_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3634_ = 0;
v___x_3635_ = lean_box(0);
v___x_3636_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3630_);
v___x_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
v___x_3638_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3627_, v_stx_3628_, v_e_3629_, v___x_3634_, v___x_3635_, v___x_3637_, v___x_3634_, v_a_3631_, v_a_3632_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3639_, lean_object* v_stx_3640_, lean_object* v_e_3641_, lean_object* v_reason_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3639_, v_stx_3640_, v_e_3641_, v_reason_3642_, v_a_3643_, v_a_3644_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec(v_reason_3642_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3647_, lean_object* v_stx_3648_, lean_object* v_e_3649_, lean_object* v_reason_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3647_, v_stx_3648_, v_e_3649_, v_reason_3650_, v_a_3652_, v_a_3653_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3659_, lean_object* v_stx_3660_, lean_object* v_e_3661_, lean_object* v_reason_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3659_, v_stx_3660_, v_e_3661_, v_reason_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_reason_3662_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3671_, lean_object* v_ctx_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_optionsPerPos_3679_; lean_object* v_currNamespace_3680_; lean_object* v_openDecls_3681_; uint8_t v_inPattern_3682_; lean_object* v_subExpr_3683_; lean_object* v_depth_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3694_; 
v_optionsPerPos_3679_ = lean_ctor_get(v_ctx_3672_, 0);
v_currNamespace_3680_ = lean_ctor_get(v_ctx_3672_, 1);
v_openDecls_3681_ = lean_ctor_get(v_ctx_3672_, 2);
v_inPattern_3682_ = lean_ctor_get_uint8(v_ctx_3672_, sizeof(void*)*5);
v_subExpr_3683_ = lean_ctor_get(v_ctx_3672_, 3);
v_depth_3684_ = lean_ctor_get(v_ctx_3672_, 4);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_ctx_3672_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3686_ = v_ctx_3672_;
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_depth_3684_);
lean_inc(v_subExpr_3683_);
lean_inc(v_openDecls_3681_);
lean_inc(v_currNamespace_3680_);
lean_inc(v_optionsPerPos_3679_);
lean_dec(v_ctx_3672_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_nat_add(v_depth_3684_, v___x_3688_);
lean_dec(v_depth_3684_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v___x_3689_);
v___x_3691_ = v___x_3686_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_optionsPerPos_3679_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_currNamespace_3680_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_openDecls_3681_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v_subExpr_3683_);
lean_ctor_set(v_reuseFailAlloc_3693_, 4, v___x_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3693_, sizeof(void*)*5, v_inPattern_3682_);
v___x_3691_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_apply_7(v_act_3671_, v___x_3691_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, lean_box(0));
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3695_, lean_object* v_ctx_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3695_, v_ctx_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3704_, lean_object* v_act_3705_, lean_object* v_ctx_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3705_, v_ctx_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3714_, lean_object* v_act_3715_, lean_object* v_ctx_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3714_, v_act_3715_, v_ctx_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
return v_res_3723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3724_, lean_object* v_e_3725_){
_start:
{
lean_object* v___y_3727_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___x_3731_ = lean_unsigned_to_nat(254u);
v___x_3732_ = lean_nat_dec_le(v___x_3731_, v_threshold_3724_);
if (v___x_3732_ == 0)
{
v___y_3727_ = v_threshold_3724_;
goto v___jp_3726_;
}
else
{
v___y_3727_ = v___x_3731_;
goto v___jp_3726_;
}
v___jp_3726_:
{
uint32_t v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3728_ = l_Lean_Expr_approxDepth(v_e_3725_);
v___x_3729_ = lean_uint32_to_nat(v___x_3728_);
v___x_3730_ = lean_nat_dec_le(v___x_3729_, v___y_3727_);
lean_dec(v___x_3729_);
return v___x_3730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3733_, lean_object* v_e_3734_){
_start:
{
uint8_t v_res_3735_; lean_object* v_r_3736_; 
v_res_3735_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3733_, v_e_3734_);
lean_dec_ref(v_e_3734_);
lean_dec(v_threshold_3733_);
v_r_3736_ = lean_box(v_res_3735_);
return v_r_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
uint8_t v___x_3747_; 
v___x_3747_ = l_Lean_Expr_isAtomic(v_e_3739_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
lean_inc(v_a_3745_);
lean_inc_ref(v_a_3744_);
lean_inc(v_a_3743_);
lean_inc_ref(v_a_3742_);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_3749_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3748_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3793_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3793_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3793_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_unbox(v_a_3750_);
if (v___x_3754_ == 0)
{
lean_object* v_depth_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_del_object(v___x_3752_);
v_depth_3755_ = lean_ctor_get(v_a_3740_, 4);
lean_inc(v_depth_3755_);
v___x_3756_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3757_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3756_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3780_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3780_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3780_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3762_ = lean_nat_sub(v_depth_3755_, v_a_3758_);
lean_dec(v_depth_3755_);
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_nat_dec_lt(v___x_3763_, v___x_3762_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec(v___x_3762_);
lean_dec(v_a_3758_);
lean_dec(v_a_3750_);
v___x_3765_ = lean_box(v___x_3764_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3765_);
v___x_3767_ = v___x_3760_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3769_ = lean_unsigned_to_nat(2u);
v___x_3770_ = lean_nat_shiftr(v_a_3758_, v___x_3769_);
lean_dec(v_a_3758_);
v___x_3771_ = lean_nat_sub(v___x_3770_, v___x_3762_);
lean_dec(v___x_3762_);
lean_dec(v___x_3770_);
v___x_3772_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3771_, v_e_3739_);
lean_dec(v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3775_; 
lean_dec(v_a_3750_);
v___x_3773_ = lean_box(v___x_3764_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3773_);
v___x_3775_ = v___x_3760_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
else
{
lean_object* v___x_3778_; 
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v_a_3750_);
v___x_3778_ = v___x_3760_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3750_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_depth_3755_);
lean_dec(v_a_3750_);
v_a_3781_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3757_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3757_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec(v_a_3750_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
v___x_3789_ = lean_box(v___x_3747_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3789_);
v___x_3791_ = v___x_3752_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
return v___x_3749_;
}
}
else
{
uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
v___x_3794_ = 0;
v___x_3795_ = lean_box(v___x_3794_);
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec_ref(v_e_3797_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
uint8_t v___x_3816_; 
v___x_3816_ = l_Lean_Expr_isAtomic(v_e_3808_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
lean_inc_ref(v_a_3811_);
lean_inc(v_a_3810_);
lean_inc_ref(v_a_3809_);
v___x_3818_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3817_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3869_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3821_ = v___x_3818_;
v_isShared_3822_ = v_isSharedCheck_3869_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3869_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___y_3824_; uint8_t v___x_3849_; 
v___x_3849_ = lean_unbox(v_a_3819_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
lean_del_object(v___x_3821_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
lean_inc_ref(v_a_3811_);
lean_inc_ref(v_e_3808_);
v___x_3850_ = l_Lean_Meta_isProof(v_e_3808_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3850_) == 0)
{
v___y_3824_ = v___x_3850_;
goto v___jp_3823_;
}
else
{
lean_object* v_a_3851_; uint8_t v___y_3853_; uint8_t v___x_3863_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
v___x_3863_ = l_Lean_Exception_isInterrupt(v_a_3851_);
if (v___x_3863_ == 0)
{
uint8_t v___x_3864_; 
v___x_3864_ = l_Lean_Exception_isRuntime(v_a_3851_);
v___y_3853_ = v___x_3864_;
goto v___jp_3852_;
}
else
{
lean_dec(v_a_3851_);
v___y_3853_ = v___x_3863_;
goto v___jp_3852_;
}
v___jp_3852_:
{
if (v___y_3853_ == 0)
{
lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_a_3819_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; 
v_unused_3862_ = lean_ctor_get(v___x_3850_, 0);
lean_dec(v_unused_3862_);
v___x_3855_ = v___x_3850_;
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
else
{
lean_dec(v___x_3850_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = lean_box(v___y_3853_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set_tag(v___x_3855_, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3857_);
v___x_3859_ = v___x_3855_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
else
{
v___y_3824_ = v___x_3850_;
goto v___jp_3823_;
}
}
}
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
lean_dec(v_a_3819_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
v___x_3865_ = lean_box(v___x_3816_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3865_);
v___x_3867_ = v___x_3821_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
v___jp_3823_:
{
if (lean_obj_tag(v___y_3824_) == 0)
{
lean_object* v_a_3825_; uint8_t v___x_3826_; 
v_a_3825_ = lean_ctor_get(v___y_3824_, 0);
v___x_3826_ = lean_unbox(v_a_3825_);
if (v___x_3826_ == 0)
{
lean_dec(v_a_3819_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
return v___y_3824_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_inc(v_a_3825_);
lean_dec_ref(v___y_3824_);
v___x_3827_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3828_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3827_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3840_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3840_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3840_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
uint8_t v___x_3833_; 
v___x_3833_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3829_, v_e_3808_);
lean_dec_ref(v_e_3808_);
lean_dec(v_a_3829_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3835_; 
lean_dec(v_a_3819_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_a_3825_);
v___x_3835_ = v___x_3831_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3825_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
else
{
lean_object* v___x_3838_; 
lean_dec(v_a_3825_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_a_3819_);
v___x_3838_ = v___x_3831_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3819_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v_a_3825_);
lean_dec(v_a_3819_);
lean_dec_ref(v_e_3808_);
v_a_3841_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3828_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3828_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
else
{
lean_dec(v_a_3819_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
return v___y_3824_;
}
}
}
}
else
{
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
return v___x_3818_;
}
}
else
{
uint8_t v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec_ref(v_e_3808_);
v___x_3870_ = 0;
v___x_3871_ = lean_box(v___x_3870_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_ref_3896_; uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_ref_3896_ = lean_ctor_get(v_a_3894_, 5);
v___x_3897_ = 0;
v___x_3898_ = l_Lean_SourceInfo_fromRef(v_ref_3896_, v___x_3897_);
v___x_3899_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3900_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3898_);
v___x_3901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3898_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3899_, v___x_3901_);
v___x_3903_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3902_, v_a_3891_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v_a_3906_; lean_object* v___x_3907_; lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3891_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3891_);
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
lean_inc(v_a_3904_);
v___x_3909_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3906_, v_a_3904_, v_a_3908_, v_reason_3890_, v_a_3892_, v_a_3893_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v___x_3909_, 0);
lean_dec(v_unused_3917_);
v___x_3911_ = v___x_3909_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_dec(v___x_3909_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v_a_3904_);
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3904_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_a_3904_);
v_a_3918_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3909_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3909_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec_ref(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_reason_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3938_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_reason_3942_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v___x_3959_; 
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
v___x_3959_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3959_;
}
else
{
lean_object* v_head_3960_; lean_object* v_tail_3961_; lean_object* v___x_3962_; 
v_head_3960_ = lean_ctor_get(v_x_3951_, 0);
lean_inc(v_head_3960_);
v_tail_3961_ = lean_ctor_get(v_x_3951_, 1);
lean_inc(v_tail_3961_);
lean_dec_ref(v_x_3951_);
lean_inc(v___y_3957_);
lean_inc_ref(v___y_3956_);
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3954_);
lean_inc(v___y_3953_);
lean_inc_ref(v___y_3952_);
v___x_3962_ = lean_apply_7(v_head_3960_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, lean_box(0));
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_dec(v_tail_3961_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v___x_3962_;
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3964_; uint8_t v___y_3966_; uint8_t v___x_3970_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
v___x_3964_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3970_ = l_Lean_Exception_isInterrupt(v_a_3963_);
if (v___x_3970_ == 0)
{
uint8_t v___x_3971_; 
lean_inc(v_a_3963_);
v___x_3971_ = l_Lean_Exception_isRuntime(v_a_3963_);
v___y_3966_ = v___x_3971_;
goto v___jp_3965_;
}
else
{
v___y_3966_ = v___x_3970_;
goto v___jp_3965_;
}
v___jp_3965_:
{
if (v___y_3966_ == 0)
{
if (lean_obj_tag(v_a_3963_) == 0)
{
lean_dec_ref(v_a_3963_);
lean_dec(v_tail_3961_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v___x_3962_;
}
else
{
lean_object* v_id_3967_; uint8_t v___x_3968_; 
v_id_3967_ = lean_ctor_get(v_a_3963_, 0);
lean_inc(v_id_3967_);
lean_dec_ref(v_a_3963_);
v___x_3968_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3964_, v_id_3967_);
lean_dec(v_id_3967_);
if (v___x_3968_ == 0)
{
lean_dec(v_tail_3961_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v___x_3962_;
}
else
{
lean_dec_ref(v___x_3962_);
v_x_3951_ = v_tail_3961_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3963_);
lean_dec(v_tail_3961_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v___x_3962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; uint8_t v___y_3993_; lean_object* v___y_4001_; 
if (lean_obj_tag(v_x_3981_) == 0)
{
lean_object* v___x_4006_; 
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
v___x_4006_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; lean_object* v_env_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4007_ = lean_st_ref_get(v_a_3987_);
v_env_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc_ref(v_env_4008_);
lean_dec(v___x_4007_);
v___x_4009_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_4010_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_4009_, v_env_4008_, v_x_3981_);
lean_inc(v_a_3987_);
lean_inc_ref(v_a_3986_);
lean_inc(v_a_3985_);
lean_inc_ref(v_a_3984_);
lean_inc(v_a_3983_);
lean_inc_ref(v_a_3982_);
v___x_4011_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_4010_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4013_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref(v___x_4011_);
v___x_4013_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_4012_, v_a_3982_, v_a_3983_, v_a_3984_);
v___y_4001_ = v___x_4013_;
goto v___jp_4000_;
}
else
{
v___y_4001_ = v___x_4011_;
goto v___jp_4000_;
}
}
v___jp_3989_:
{
if (v___y_3993_ == 0)
{
if (lean_obj_tag(v___y_3992_) == 0)
{
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3990_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_x_3981_);
return v___y_3991_;
}
else
{
lean_object* v_id_3994_; uint8_t v___x_3995_; 
v_id_3994_ = lean_ctor_get(v___y_3992_, 0);
lean_inc(v_id_3994_);
lean_dec_ref(v___y_3992_);
v___x_3995_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3990_, v_id_3994_);
lean_dec(v_id_3994_);
lean_dec(v___y_3990_);
if (v___x_3995_ == 0)
{
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_x_3981_);
return v___y_3991_;
}
else
{
uint8_t v___x_3996_; 
lean_dec_ref(v___y_3991_);
v___x_3996_ = l_Lean_Name_isAtomic(v_x_3981_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Name_getRoot(v_x_3981_);
lean_dec(v_x_3981_);
v_x_3981_ = v___x_3997_;
goto _start;
}
else
{
lean_object* v___x_3999_; 
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_x_3981_);
v___x_3999_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3999_;
}
}
}
}
else
{
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3990_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_x_3981_);
return v___y_3991_;
}
}
v___jp_4000_:
{
if (lean_obj_tag(v___y_4001_) == 0)
{
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_x_3981_);
return v___y_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v_a_4002_ = lean_ctor_get(v___y_4001_, 0);
lean_inc(v_a_4002_);
v___x_4003_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4004_ = l_Lean_Exception_isInterrupt(v_a_4002_);
if (v___x_4004_ == 0)
{
uint8_t v___x_4005_; 
lean_inc(v_a_4002_);
v___x_4005_ = l_Lean_Exception_isRuntime(v_a_4002_);
v___y_3990_ = v___x_4003_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v_a_4002_;
v___y_3993_ = v___x_4005_;
goto v___jp_3989_;
}
else
{
v___y_3990_ = v___x_4003_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v_a_4002_;
v___y_3993_ = v___x_4004_;
goto v___jp_3989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; lean_object* v_env_4030_; lean_object* v___x_4031_; lean_object* v_mctx_4032_; lean_object* v_lctx_4033_; lean_object* v_options_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4029_ = lean_st_ref_get(v___y_4027_);
v_env_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc_ref(v_env_4030_);
lean_dec(v___x_4029_);
v___x_4031_ = lean_st_ref_get(v___y_4025_);
v_mctx_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc_ref(v_mctx_4032_);
lean_dec(v___x_4031_);
v_lctx_4033_ = lean_ctor_get(v___y_4024_, 2);
v_options_4034_ = lean_ctor_get(v___y_4026_, 2);
lean_inc_ref(v_options_4034_);
lean_inc_ref(v_lctx_4033_);
v___x_4035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4035_, 0, v_env_4030_);
lean_ctor_set(v___x_4035_, 1, v_mctx_4032_);
lean_ctor_set(v___x_4035_, 2, v_lctx_4033_);
lean_ctor_set(v___x_4035_, 3, v_options_4034_);
v___x_4036_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
lean_ctor_set(v___x_4036_, 1, v_msgData_4023_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_ref_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4061_; 
v_ref_4051_ = lean_ctor_get(v___y_4048_, 5);
v___x_4052_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_inc(v_ref_4051_);
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v_ref_4051_);
lean_ctor_set(v___x_4057_, 1, v_a_4053_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 1);
lean_ctor_set(v___x_4055_, 0, v___x_4057_);
v___x_4059_ = v___x_4055_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4068_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
lean_inc(v___y_4078_);
lean_inc_ref(v___y_4077_);
lean_inc(v___y_4076_);
lean_inc_ref(v___y_4075_);
lean_inc(v_a_4072_);
v___x_4080_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_a_4072_);
return v___x_4080_;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4082_; uint8_t v___y_4084_; uint8_t v___x_4100_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
v___x_4082_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4100_ = l_Lean_Exception_isInterrupt(v_a_4081_);
if (v___x_4100_ == 0)
{
uint8_t v___x_4101_; 
lean_inc(v_a_4081_);
v___x_4101_ = l_Lean_Exception_isRuntime(v_a_4081_);
v___y_4084_ = v___x_4101_;
goto v___jp_4083_;
}
else
{
v___y_4084_ = v___x_4100_;
goto v___jp_4083_;
}
v___jp_4083_:
{
if (v___y_4084_ == 0)
{
if (lean_obj_tag(v_a_4081_) == 0)
{
lean_dec_ref(v_a_4081_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_a_4072_);
return v___x_4080_;
}
else
{
lean_object* v_id_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4098_; 
v_id_4085_ = lean_ctor_get(v_a_4081_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_a_4081_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; 
v_unused_4099_ = lean_ctor_get(v_a_4081_, 1);
lean_dec(v_unused_4099_);
v___x_4087_ = v_a_4081_;
v_isShared_4088_ = v_isSharedCheck_4098_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_id_4085_);
lean_dec(v_a_4081_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4098_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
uint8_t v___x_4089_; 
v___x_4089_ = l_Lean_instBEqInternalExceptionId_beq(v___x_4082_, v_id_4085_);
lean_dec(v_id_4085_);
if (v___x_4089_ == 0)
{
lean_del_object(v___x_4087_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_a_4072_);
return v___x_4080_;
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
lean_dec_ref(v___x_4080_);
v___x_4090_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_4091_ = l_Lean_MessageData_ofName(v_a_4072_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 7);
lean_ctor_set(v___x_4087_, 1, v___x_4091_);
lean_ctor_set(v___x_4087_, 0, v___x_4090_);
v___x_4093_ = v___x_4087_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__12_spec__16___redArg___closed__3);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_4095_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v___x_4096_;
}
}
}
}
}
else
{
lean_dec(v_a_4081_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_a_4072_);
return v___x_4080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; lean_object* v_a_4120_; lean_object* v___x_4121_; 
v___x_4119_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4112_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
lean_inc(v___y_4117_);
lean_inc_ref(v___y_4116_);
lean_inc(v___y_4115_);
lean_inc_ref(v___y_4114_);
v___x_4121_ = lean_infer_type(v_a_4120_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4124_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4122_, v___x_4123_, v_x_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4124_;
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec_ref(v_x_4111_);
v_a_4125_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4121_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4121_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v_res_4141_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1));
v___x_4160_ = l_String_toRawSubstring_x27(v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4218_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_));
v___x_4219_ = l_Lean_Core_checkSystem(v___x_4218_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_dec_ref(v___x_4219_);
v___x_4220_ = lean_st_ref_get(v_a_4212_);
v___x_4221_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4222_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4221_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v_steps_4224_; uint8_t v___x_4225_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref(v___x_4222_);
v_steps_4224_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_steps_4224_);
lean_dec(v___x_4220_);
v___x_4225_ = lean_nat_dec_le(v_a_4223_, v_steps_4224_);
lean_dec(v_steps_4224_);
lean_dec(v_a_4223_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v_steps_4227_; lean_object* v_infos_4228_; lean_object* v_holeIter_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4400_; 
v___x_4226_ = lean_st_ref_take(v_a_4212_);
v_steps_4227_ = lean_ctor_get(v___x_4226_, 0);
v_infos_4228_ = lean_ctor_get(v___x_4226_, 1);
v_holeIter_4229_ = lean_ctor_get(v___x_4226_, 2);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4231_ = v___x_4226_;
v_isShared_4232_ = v_isSharedCheck_4400_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_holeIter_4229_);
lean_inc(v_infos_4228_);
lean_inc(v_steps_4227_);
lean_dec(v___x_4226_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4400_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_nat_add(v_steps_4227_, v___x_4233_);
lean_dec(v_steps_4227_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4234_);
v___x_4236_ = v___x_4231_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_infos_4228_);
lean_ctor_set(v_reuseFailAlloc_4399_, 2, v_holeIter_4229_);
v___x_4236_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_st_ref_set(v_a_4212_, v___x_4236_);
v___x_4238_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4211_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4240_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref(v___x_4238_);
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4240_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4239_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; uint8_t v___x_4242_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = lean_unbox(v_a_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
lean_inc(v_a_4239_);
v___x_4243_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4239_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; uint8_t v___x_4245_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref(v___x_4243_);
v___x_4245_ = lean_unbox(v_a_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec(v_a_4241_);
v___x_4246_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref(v___x_4246_);
v___f_4248_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4248_, 0, v_a_4247_);
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4249_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4248_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___y_4252_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v___x_4298_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4299_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4298_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; uint8_t v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
v___x_4301_ = lean_unbox(v_a_4300_);
lean_dec(v_a_4300_);
if (v___x_4301_ == 0)
{
lean_dec(v_a_4239_);
v___y_4252_ = v___x_4299_;
goto v___jp_4251_;
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
lean_dec_ref(v___x_4299_);
v___x_4302_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4303_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4302_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; uint8_t v___x_4305_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
v___x_4305_ = lean_unbox(v_a_4304_);
lean_dec(v_a_4304_);
if (v___x_4305_ == 0)
{
lean_dec(v_a_4239_);
v___y_4252_ = v___x_4303_;
goto v___jp_4251_;
}
else
{
uint8_t v___x_4306_; 
v___x_4306_ = l_Lean_Expr_isMData(v_a_4239_);
lean_dec(v_a_4239_);
if (v___x_4306_ == 0)
{
v___y_4252_ = v___x_4303_;
goto v___jp_4251_;
}
else
{
lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v_a_4244_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4313_ == 0)
{
lean_object* v_unused_4314_; 
v_unused_4314_ = lean_ctor_get(v___x_4303_, 0);
lean_dec(v_unused_4314_);
v___x_4308_ = v___x_4303_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_dec(v___x_4303_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v_a_4250_);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4250_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
else
{
lean_dec(v_a_4239_);
v___y_4252_ = v___x_4303_;
goto v___jp_4251_;
}
}
}
else
{
lean_dec(v_a_4239_);
v___y_4252_ = v___x_4299_;
goto v___jp_4251_;
}
v___jp_4251_:
{
if (lean_obj_tag(v___y_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4289_; 
v_a_4253_ = lean_ctor_get(v___y_4252_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___y_4252_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4255_ = v___y_4252_;
v_isShared_4256_ = v_isSharedCheck_4289_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___y_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4289_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_unbox(v_a_4253_);
lean_dec(v_a_4253_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4259_; 
lean_dec(v_a_4244_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v_a_4250_);
v___x_4259_ = v___x_4255_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4250_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_del_object(v___x_4255_);
v___x_4261_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
lean_inc_ref(v_a_4215_);
lean_inc_ref(v_a_4211_);
v___x_4262_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4261_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v_ref_4264_; lean_object* v_quotContext_4265_; lean_object* v_currMacroScope_4266_; uint8_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___x_4262_);
v_ref_4264_ = lean_ctor_get(v_a_4215_, 5);
lean_inc(v_ref_4264_);
v_quotContext_4265_ = lean_ctor_get(v_a_4215_, 10);
lean_inc(v_quotContext_4265_);
v_currMacroScope_4266_ = lean_ctor_get(v_a_4215_, 11);
lean_inc(v_currMacroScope_4266_);
lean_dec_ref(v_a_4215_);
v___x_4267_ = lean_unbox(v_a_4244_);
lean_dec(v_a_4244_);
v___x_4268_ = l_Lean_SourceInfo_fromRef(v_ref_4264_, v___x_4267_);
lean_dec(v_ref_4264_);
v___x_4269_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4270_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4271_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc(v___x_4268_);
v___x_4272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4268_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4274_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4275_ = lean_box(0);
v___x_4276_ = l_Lean_addMacroScope(v_quotContext_4265_, v___x_4275_, v_currMacroScope_4266_);
v___x_4277_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
lean_inc(v___x_4268_);
v___x_4278_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4268_);
lean_ctor_set(v___x_4278_, 1, v___x_4274_);
lean_ctor_set(v___x_4278_, 2, v___x_4276_);
lean_ctor_set(v___x_4278_, 3, v___x_4277_);
lean_inc(v___x_4268_);
v___x_4279_ = l_Lean_Syntax_node1(v___x_4268_, v___x_4273_, v___x_4278_);
lean_inc(v___x_4268_);
v___x_4280_ = l_Lean_Syntax_node2(v___x_4268_, v___x_4270_, v___x_4272_, v___x_4279_);
v___x_4281_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
lean_inc(v___x_4268_);
v___x_4282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4268_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
lean_inc(v___x_4268_);
v___x_4284_ = l_Lean_Syntax_node1(v___x_4268_, v___x_4283_, v_a_4263_);
v___x_4285_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
lean_inc(v___x_4268_);
v___x_4286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4268_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_Syntax_node5(v___x_4268_, v___x_4269_, v___x_4280_, v_a_4250_, v___x_4282_, v___x_4284_, v___x_4286_);
v___x_4288_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4287_, v_a_4211_);
lean_dec_ref(v_a_4211_);
return v___x_4288_;
}
else
{
lean_dec(v_a_4250_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4211_);
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec(v_a_4250_);
lean_dec(v_a_4244_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4290_ = lean_ctor_get(v___y_4252_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___y_4252_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___y_4252_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___y_4252_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
}
else
{
lean_dec(v_a_4244_);
lean_dec(v_a_4239_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v___x_4249_;
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_a_4244_);
lean_dec(v_a_4239_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4315_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4246_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4246_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
lean_dec(v_a_4244_);
lean_dec(v_a_4239_);
v___x_4323_ = lean_box(1);
v___x_4324_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4323_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4215_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref(v___x_4324_);
v___x_4326_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
lean_inc(v_a_4216_);
lean_inc_ref(v_a_4215_);
lean_inc(v_a_4214_);
lean_inc_ref(v_a_4213_);
lean_inc(v_a_4212_);
lean_inc_ref(v_a_4211_);
v___x_4327_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4326_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4364_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
uint8_t v___x_4332_; 
v___x_4332_ = lean_unbox(v_a_4328_);
lean_dec(v_a_4328_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4334_; 
lean_dec(v_a_4241_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v_a_4325_);
v___x_4334_ = v___x_4330_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4325_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
else
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
lean_del_object(v___x_4330_);
v___x_4336_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
lean_inc_ref(v_a_4215_);
lean_inc_ref(v_a_4211_);
v___x_4337_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4336_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v_ref_4339_; lean_object* v_quotContext_4340_; lean_object* v_currMacroScope_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
lean_dec_ref(v___x_4337_);
v_ref_4339_ = lean_ctor_get(v_a_4215_, 5);
lean_inc(v_ref_4339_);
v_quotContext_4340_ = lean_ctor_get(v_a_4215_, 10);
lean_inc(v_quotContext_4340_);
v_currMacroScope_4341_ = lean_ctor_get(v_a_4215_, 11);
lean_inc(v_currMacroScope_4341_);
lean_dec_ref(v_a_4215_);
v___x_4342_ = lean_unbox(v_a_4241_);
lean_dec(v_a_4241_);
v___x_4343_ = l_Lean_SourceInfo_fromRef(v_ref_4339_, v___x_4342_);
lean_dec(v_ref_4339_);
v___x_4344_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4345_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4346_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc(v___x_4343_);
v___x_4347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4343_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4349_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4350_ = lean_box(0);
v___x_4351_ = l_Lean_addMacroScope(v_quotContext_4340_, v___x_4350_, v_currMacroScope_4341_);
v___x_4352_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
lean_inc(v___x_4343_);
v___x_4353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4343_);
lean_ctor_set(v___x_4353_, 1, v___x_4349_);
lean_ctor_set(v___x_4353_, 2, v___x_4351_);
lean_ctor_set(v___x_4353_, 3, v___x_4352_);
lean_inc(v___x_4343_);
v___x_4354_ = l_Lean_Syntax_node1(v___x_4343_, v___x_4348_, v___x_4353_);
lean_inc(v___x_4343_);
v___x_4355_ = l_Lean_Syntax_node2(v___x_4343_, v___x_4345_, v___x_4347_, v___x_4354_);
v___x_4356_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
lean_inc(v___x_4343_);
v___x_4357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4343_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__7));
lean_inc(v___x_4343_);
v___x_4359_ = l_Lean_Syntax_node1(v___x_4343_, v___x_4358_, v_a_4338_);
v___x_4360_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
lean_inc(v___x_4343_);
v___x_4361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4343_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = l_Lean_Syntax_node5(v___x_4343_, v___x_4344_, v___x_4355_, v_a_4325_, v___x_4357_, v___x_4359_, v___x_4361_);
v___x_4363_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4362_, v_a_4211_);
lean_dec_ref(v_a_4211_);
return v___x_4363_;
}
else
{
lean_dec(v_a_4325_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4211_);
return v___x_4337_;
}
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_a_4325_);
lean_dec(v_a_4241_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4365_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4327_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4327_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_dec(v_a_4241_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v___x_4324_;
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4241_);
lean_dec(v_a_4239_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4373_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4243_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4243_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec(v_a_4241_);
lean_dec(v_a_4239_);
lean_dec(v_a_4216_);
lean_dec(v_a_4214_);
v___x_4381_ = lean_box(0);
v___x_4382_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4381_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4215_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v___x_4382_;
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec(v_a_4239_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4383_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4240_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4240_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4391_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4238_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4238_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
lean_dec(v_a_4216_);
lean_dec(v_a_4214_);
v___x_4401_ = lean_box(2);
v___x_4402_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4401_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4215_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v___x_4402_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v___x_4220_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4403_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4222_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4222_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
v_a_4411_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4219_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4219_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4419_, lean_object* v_msg_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_msg_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4427_, v_msg_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4445_, lean_object* v_x_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4445_, v_x_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4455_, lean_object* v_stx_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
lean_inc_ref(v___y_4457_);
v___x_4460_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4456_, v___y_4457_, v___y_4458_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = lean_box(0);
lean_inc(v___y_4458_);
lean_inc_ref(v___y_4457_);
v___x_4463_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4461_, v___x_4462_, v___y_4457_, v___y_4458_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; uint8_t v___x_4465_; lean_object* v___x_4466_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref(v___x_4463_);
v___x_4465_ = 0;
lean_inc(v_a_4464_);
v___x_4466_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0(v_a_4464_, v___x_4465_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4473_ == 0)
{
lean_object* v_unused_4474_; 
v_unused_4474_ = lean_ctor_get(v___x_4466_, 0);
lean_dec(v_unused_4474_);
v___x_4468_ = v___x_4466_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_dec(v___x_4466_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v_a_4464_);
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4464_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_a_4464_);
v_a_4475_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4466_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4466_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
else
{
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v___x_4463_;
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
v_a_4483_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4460_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4460_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4491_, lean_object* v_stx_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
uint8_t v_x_625__boxed_4496_; lean_object* v_res_4497_; 
v_x_625__boxed_4496_ = lean_unbox(v_x_4491_);
v_res_4497_ = l_Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_625__boxed_4496_, v_stx_4492_, v___y_4493_, v___y_4494_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4523_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4524_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4522_, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4530_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4531_ = l_Lean_addBuiltinDocString(v___x_4529_, v___x_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4560_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4561_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4562_ = l_Lean_addBuiltinDeclarationRanges(v___x_4560_, v___x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___f_4572_; lean_object* v___x_7577__overap_4573_; lean_object* v___x_4574_; 
v___f_4572_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_7577__overap_4573_ = lean_panic_fn(v___f_4572_, v_msg_4566_);
v___x_4574_ = lean_apply_5(v___x_7577__overap_4573_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, lean_box(0));
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4582_, lean_object* v_msg_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v___x_4589_; 
v___x_4589_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4590_, lean_object* v_msg_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4590_, v_msg_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
return v_res_4597_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4598_, lean_object* v_opt_4599_){
_start:
{
lean_object* v_name_4600_; lean_object* v_defValue_4601_; lean_object* v_map_4602_; lean_object* v___x_4603_; 
v_name_4600_ = lean_ctor_get(v_opt_4599_, 0);
v_defValue_4601_ = lean_ctor_get(v_opt_4599_, 1);
v_map_4602_ = lean_ctor_get(v_opts_4598_, 0);
v___x_4603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4602_, v_name_4600_);
if (lean_obj_tag(v___x_4603_) == 0)
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_unbox(v_defValue_4601_);
return v___x_4604_;
}
else
{
lean_object* v_val_4605_; 
v_val_4605_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_val_4605_);
lean_dec_ref(v___x_4603_);
if (lean_obj_tag(v_val_4605_) == 1)
{
uint8_t v_v_4606_; 
v_v_4606_ = lean_ctor_get_uint8(v_val_4605_, 0);
lean_dec_ref(v_val_4605_);
return v_v_4606_;
}
else
{
uint8_t v___x_4607_; 
lean_dec(v_val_4605_);
v___x_4607_ = lean_unbox(v_defValue_4601_);
return v___x_4607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4608_, lean_object* v_opt_4609_){
_start:
{
uint8_t v_res_4610_; lean_object* v_r_4611_; 
v_res_4610_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4608_, v_opt_4609_);
lean_dec_ref(v_opt_4609_);
lean_dec_ref(v_opts_4608_);
v_r_4611_ = lean_box(v_res_4610_);
return v_r_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_opts_4612_, lean_object* v_opt_4613_){
_start:
{
lean_object* v_name_4614_; lean_object* v_defValue_4615_; lean_object* v_map_4616_; lean_object* v___x_4617_; 
v_name_4614_ = lean_ctor_get(v_opt_4613_, 0);
v_defValue_4615_ = lean_ctor_get(v_opt_4613_, 1);
v_map_4616_ = lean_ctor_get(v_opts_4612_, 0);
v___x_4617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4616_, v_name_4614_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_inc(v_defValue_4615_);
return v_defValue_4615_;
}
else
{
lean_object* v_val_4618_; 
v_val_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_val_4618_);
lean_dec_ref(v___x_4617_);
if (lean_obj_tag(v_val_4618_) == 3)
{
lean_object* v_v_4619_; 
v_v_4619_ = lean_ctor_get(v_val_4618_, 0);
lean_inc(v_v_4619_);
lean_dec_ref(v_val_4618_);
return v_v_4619_;
}
else
{
lean_dec(v_val_4618_);
lean_inc(v_defValue_4615_);
return v_defValue_4615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_opts_4620_, lean_object* v_opt_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v_opts_4620_, v_opt_4621_);
lean_dec_ref(v_opt_4621_);
lean_dec_ref(v_opts_4620_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(lean_object* v_e_4623_, lean_object* v___y_4624_){
_start:
{
uint8_t v___x_4626_; 
v___x_4626_ = l_Lean_Expr_hasMVar(v_e_4623_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; 
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_e_4623_);
return v___x_4627_;
}
else
{
lean_object* v___x_4628_; lean_object* v_mctx_4629_; lean_object* v___x_4630_; lean_object* v_fst_4631_; lean_object* v_snd_4632_; lean_object* v___x_4633_; lean_object* v_cache_4634_; lean_object* v_zetaDeltaFVarIds_4635_; lean_object* v_postponed_4636_; lean_object* v_diag_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4646_; 
v___x_4628_ = lean_st_ref_get(v___y_4624_);
v_mctx_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_ref(v_mctx_4629_);
lean_dec(v___x_4628_);
v___x_4630_ = l_Lean_instantiateMVarsCore(v_mctx_4629_, v_e_4623_);
v_fst_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_fst_4631_);
v_snd_4632_ = lean_ctor_get(v___x_4630_, 1);
lean_inc(v_snd_4632_);
lean_dec_ref(v___x_4630_);
v___x_4633_ = lean_st_ref_take(v___y_4624_);
v_cache_4634_ = lean_ctor_get(v___x_4633_, 1);
v_zetaDeltaFVarIds_4635_ = lean_ctor_get(v___x_4633_, 2);
v_postponed_4636_ = lean_ctor_get(v___x_4633_, 3);
v_diag_4637_ = lean_ctor_get(v___x_4633_, 4);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4646_ == 0)
{
lean_object* v_unused_4647_; 
v_unused_4647_ = lean_ctor_get(v___x_4633_, 0);
lean_dec(v_unused_4647_);
v___x_4639_ = v___x_4633_;
v_isShared_4640_ = v_isSharedCheck_4646_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_diag_4637_);
lean_inc(v_postponed_4636_);
lean_inc(v_zetaDeltaFVarIds_4635_);
lean_inc(v_cache_4634_);
lean_dec(v___x_4633_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4646_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v_snd_4632_);
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_snd_4632_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_cache_4634_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_zetaDeltaFVarIds_4635_);
lean_ctor_set(v_reuseFailAlloc_4645_, 3, v_postponed_4636_);
lean_ctor_set(v_reuseFailAlloc_4645_, 4, v_diag_4637_);
v___x_4642_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_st_ref_set(v___y_4624_, v___x_4642_);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_fst_4631_);
return v___x_4644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg___boxed(lean_object* v_e_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4648_, v___y_4649_);
lean_dec(v___y_4649_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_e_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4652_, v___y_4654_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_e_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(v_e_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4666_, lean_object* v_opt_4667_){
_start:
{
lean_object* v_name_4668_; lean_object* v_map_4669_; lean_object* v___x_4670_; 
v_name_4668_ = lean_ctor_get(v_opt_4667_, 0);
v_map_4669_ = lean_ctor_get(v_opts_4666_, 0);
v___x_4670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4669_, v_name_4668_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v___x_4671_; 
v___x_4671_ = lean_box(0);
return v___x_4671_;
}
else
{
lean_object* v_val_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4682_; 
v_val_4672_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4674_ = v___x_4670_;
v_isShared_4675_ = v_isSharedCheck_4682_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_val_4672_);
lean_dec(v___x_4670_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4682_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
if (lean_obj_tag(v_val_4672_) == 1)
{
uint8_t v_v_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v_v_4676_ = lean_ctor_get_uint8(v_val_4672_, 0);
lean_dec_ref(v_val_4672_);
v___x_4677_ = lean_box(v_v_4676_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4679_ = v___x_4674_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
else
{
lean_object* v___x_4681_; 
lean_del_object(v___x_4674_);
lean_dec(v_val_4672_);
v___x_4681_ = lean_box(0);
return v___x_4681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4683_, lean_object* v_opt_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4683_, v_opt_4684_);
lean_dec_ref(v_opt_4684_);
lean_dec_ref(v_opts_4683_);
return v_res_4685_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_x_4686_, lean_object* v_x_4687_){
_start:
{
if (lean_obj_tag(v_x_4686_) == 0)
{
if (lean_obj_tag(v_x_4687_) == 0)
{
uint8_t v___x_4688_; 
v___x_4688_ = 1;
return v___x_4688_;
}
else
{
uint8_t v___x_4689_; 
v___x_4689_ = 0;
return v___x_4689_;
}
}
else
{
if (lean_obj_tag(v_x_4687_) == 0)
{
uint8_t v___x_4690_; 
v___x_4690_ = 0;
return v___x_4690_;
}
else
{
lean_object* v_val_4691_; uint8_t v___x_4692_; 
v_val_4691_ = lean_ctor_get(v_x_4686_, 0);
v___x_4692_ = lean_unbox(v_val_4691_);
if (v___x_4692_ == 0)
{
lean_object* v_val_4693_; uint8_t v___x_4694_; 
v_val_4693_ = lean_ctor_get(v_x_4687_, 0);
v___x_4694_ = lean_unbox(v_val_4693_);
if (v___x_4694_ == 0)
{
uint8_t v___x_4695_; 
v___x_4695_ = 1;
return v___x_4695_;
}
else
{
uint8_t v___x_4696_; 
v___x_4696_ = lean_unbox(v_val_4691_);
return v___x_4696_;
}
}
else
{
lean_object* v_val_4697_; uint8_t v___x_4698_; 
v_val_4697_ = lean_ctor_get(v_x_4687_, 0);
v___x_4698_ = lean_unbox(v_val_4697_);
return v___x_4698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_x_4699_, lean_object* v_x_4700_){
_start:
{
uint8_t v_res_4701_; lean_object* v_r_4702_; 
v_res_4701_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v_x_4699_, v_x_4700_);
lean_dec(v_x_4700_);
lean_dec(v_x_4699_);
v_r_4702_ = lean_box(v_res_4701_);
return v_r_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg(lean_object* v_cls_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
v_options_4706_ = lean_ctor_get(v___y_4704_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_dec(v_cls_4703_);
v___x_4708_ = lean_box(v_hasTrace_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
else
{
lean_object* v_inheritedTraceOptions_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v_inheritedTraceOptions_4710_ = lean_ctor_get(v___y_4704_, 13);
v___x_4711_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_4712_ = l_Lean_Name_append(v___x_4711_, v_cls_4703_);
v___x_4713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4710_, v_options_4706_, v___x_4712_);
lean_dec(v___x_4712_);
v___x_4714_ = lean_box(v___x_4713_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg___boxed(lean_object* v_cls_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg(v_cls_4716_, v___y_4717_);
lean_dec_ref(v___y_4717_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object* v_cls_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg(v_cls_4720_, v___y_4723_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object* v_cls_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7(v_cls_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object* v_o_4734_, lean_object* v_k_4735_, uint8_t v_v_4736_){
_start:
{
lean_object* v_map_4737_; uint8_t v_hasTrace_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4752_; 
v_map_4737_ = lean_ctor_get(v_o_4734_, 0);
v_hasTrace_4738_ = lean_ctor_get_uint8(v_o_4734_, sizeof(void*)*1);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_o_4734_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4740_ = v_o_4734_;
v_isShared_4741_ = v_isSharedCheck_4752_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_map_4737_);
lean_dec(v_o_4734_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4752_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4742_, 0, v_v_4736_);
lean_inc(v_k_4735_);
v___x_4743_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4735_, v___x_4742_, v_map_4737_);
if (v_hasTrace_4738_ == 0)
{
lean_object* v___x_4744_; uint8_t v___x_4745_; lean_object* v___x_4747_; 
v___x_4744_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_4745_ = l_Lean_Name_isPrefixOf(v___x_4744_, v_k_4735_);
lean_dec(v_k_4735_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v___x_4743_);
v___x_4747_ = v___x_4740_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4743_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*1, v___x_4745_);
return v___x_4747_;
}
}
else
{
lean_object* v___x_4750_; 
lean_dec(v_k_4735_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v___x_4743_);
v___x_4750_ = v___x_4740_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4743_);
lean_ctor_set_uint8(v_reuseFailAlloc_4751_, sizeof(void*)*1, v_hasTrace_4738_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object* v_o_4753_, lean_object* v_k_4754_, lean_object* v_v_4755_){
_start:
{
uint8_t v_v_boxed_4756_; lean_object* v_res_4757_; 
v_v_boxed_4756_ = lean_unbox(v_v_4755_);
v_res_4757_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_o_4753_, v_k_4754_, v_v_boxed_4756_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4758_, lean_object* v_opt_4759_, uint8_t v_val_4760_){
_start:
{
lean_object* v_name_4761_; lean_object* v___x_4762_; 
v_name_4761_ = lean_ctor_get(v_opt_4759_, 0);
lean_inc(v_name_4761_);
lean_dec_ref(v_opt_4759_);
v___x_4762_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_opts_4758_, v_name_4761_, v_val_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4763_, lean_object* v_opt_4764_, lean_object* v_val_4765_){
_start:
{
uint8_t v_val_boxed_4766_; lean_object* v_res_4767_; 
v_val_boxed_4766_ = lean_unbox(v_val_4765_);
v_res_4767_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4763_, v_opt_4764_, v_val_boxed_4766_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8(lean_object* v_cls_4768_, lean_object* v_msg_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v_ref_4775_; lean_object* v___x_4776_; lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4821_; 
v_ref_4775_ = lean_ctor_get(v___y_4772_, 5);
v___x_4776_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4821_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4821_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v_traceState_4782_; lean_object* v_env_4783_; lean_object* v_nextMacroScope_4784_; lean_object* v_ngen_4785_; lean_object* v_auxDeclNGen_4786_; lean_object* v_cache_4787_; lean_object* v_messages_4788_; lean_object* v_infoState_4789_; lean_object* v_snapshotTasks_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4820_; 
v___x_4781_ = lean_st_ref_take(v___y_4773_);
v_traceState_4782_ = lean_ctor_get(v___x_4781_, 4);
v_env_4783_ = lean_ctor_get(v___x_4781_, 0);
v_nextMacroScope_4784_ = lean_ctor_get(v___x_4781_, 1);
v_ngen_4785_ = lean_ctor_get(v___x_4781_, 2);
v_auxDeclNGen_4786_ = lean_ctor_get(v___x_4781_, 3);
v_cache_4787_ = lean_ctor_get(v___x_4781_, 5);
v_messages_4788_ = lean_ctor_get(v___x_4781_, 6);
v_infoState_4789_ = lean_ctor_get(v___x_4781_, 7);
v_snapshotTasks_4790_ = lean_ctor_get(v___x_4781_, 8);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4792_ = v___x_4781_;
v_isShared_4793_ = v_isSharedCheck_4820_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_snapshotTasks_4790_);
lean_inc(v_infoState_4789_);
lean_inc(v_messages_4788_);
lean_inc(v_cache_4787_);
lean_inc(v_traceState_4782_);
lean_inc(v_auxDeclNGen_4786_);
lean_inc(v_ngen_4785_);
lean_inc(v_nextMacroScope_4784_);
lean_inc(v_env_4783_);
lean_dec(v___x_4781_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4820_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
uint64_t v_tid_4794_; lean_object* v_traces_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4819_; 
v_tid_4794_ = lean_ctor_get_uint64(v_traceState_4782_, sizeof(void*)*1);
v_traces_4795_ = lean_ctor_get(v_traceState_4782_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_traceState_4782_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4797_ = v_traceState_4782_;
v_isShared_4798_ = v_isSharedCheck_4819_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_traces_4795_);
lean_dec(v_traceState_4782_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4819_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4799_; double v___x_4800_; uint8_t v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4809_; 
v___x_4799_ = lean_box(0);
v___x_4800_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__0);
v___x_4801_ = 0;
v___x_4802_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__1));
v___x_4803_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4803_, 0, v_cls_4768_);
lean_ctor_set(v___x_4803_, 1, v___x_4799_);
lean_ctor_set(v___x_4803_, 2, v___x_4802_);
lean_ctor_set_float(v___x_4803_, sizeof(void*)*3, v___x_4800_);
lean_ctor_set_float(v___x_4803_, sizeof(void*)*3 + 8, v___x_4800_);
lean_ctor_set_uint8(v___x_4803_, sizeof(void*)*3 + 16, v___x_4801_);
v___x_4804_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0_spec__3___closed__2));
v___x_4805_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4803_);
lean_ctor_set(v___x_4805_, 1, v_a_4777_);
lean_ctor_set(v___x_4805_, 2, v___x_4804_);
lean_inc(v_ref_4775_);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v_ref_4775_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = l_Lean_PersistentArray_push___redArg(v_traces_4795_, v___x_4806_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4807_);
v___x_4809_ = v___x_4797_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4807_);
lean_ctor_set_uint64(v_reuseFailAlloc_4818_, sizeof(void*)*1, v_tid_4794_);
v___x_4809_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4811_; 
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 4, v___x_4809_);
v___x_4811_ = v___x_4792_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_env_4783_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_nextMacroScope_4784_);
lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_ngen_4785_);
lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_auxDeclNGen_4786_);
lean_ctor_set(v_reuseFailAlloc_4817_, 4, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4817_, 5, v_cache_4787_);
lean_ctor_set(v_reuseFailAlloc_4817_, 6, v_messages_4788_);
lean_ctor_set(v_reuseFailAlloc_4817_, 7, v_infoState_4789_);
lean_ctor_set(v_reuseFailAlloc_4817_, 8, v_snapshotTasks_4790_);
v___x_4811_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4812_ = lean_st_ref_set(v___y_4773_, v___x_4811_);
v___x_4813_ = lean_box(0);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4813_);
v___x_4815_ = v___x_4779_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8___boxed(lean_object* v_cls_4822_, lean_object* v_msg_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8(v_cls_4822_, v_msg_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
return v_res_4829_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4833_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4834_ = lean_unsigned_to_nat(18u);
v___x_4835_ = lean_unsigned_to_nat(511u);
v___x_4836_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4837_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4838_ = l_mkPanicMessageWithDecl(v___x_4837_, v___x_4836_, v___x_4835_, v___x_4834_, v___x_4833_);
return v___x_4838_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4840_ = lean_unsigned_to_nat(2u);
v___x_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
lean_ctor_set(v___x_4841_, 1, v___x_4839_);
return v___x_4841_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4842_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4843_ = lean_box(1);
v___x_4844_ = lean_unsigned_to_nat(0u);
v___x_4845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
lean_ctor_set(v___x_4845_, 1, v___x_4843_);
lean_ctor_set(v___x_4845_, 2, v___x_4842_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4851_, lean_object* v_optionsPerPos_4852_, lean_object* v_delab_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v_fst_4860_; lean_object* v_snd_4861_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; uint8_t v___y_4872_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v_optionsPerPos_4894_; lean_object* v___y_4895_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4930_; lean_object* v_e_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4949_; lean_object* v_e_4950_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4954_; lean_object* v___x_4966_; 
lean_inc(v_a_4857_);
lean_inc_ref(v_a_4856_);
v___x_4966_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4851_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5106_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_4969_ = v___x_4966_;
v_isShared_4970_ = v_isSharedCheck_5106_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4966_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5106_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___y_4972_; lean_object* v___y_4973_; uint8_t v___y_4974_; uint8_t v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_5006_; lean_object* v___y_5007_; uint8_t v___y_5008_; lean_object* v___y_5009_; uint8_t v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; uint8_t v___y_5013_; lean_object* v_opts_5035_; lean_object* v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; uint8_t v___y_5053_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; uint8_t v___y_5064_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5105_; 
v___x_5084_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5085_ = l_Lean_isTracingEnabledFor___at___00Lean_PrettyPrinter_delabCore_spec__7___redArg(v___x_5084_, v_a_4856_);
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5088_ = v___x_5085_;
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
v___jp_4971_:
{
lean_object* v_fileName_4979_; lean_object* v_fileMap_4980_; lean_object* v_currRecDepth_4981_; lean_object* v_ref_4982_; lean_object* v_currNamespace_4983_; lean_object* v_openDecls_4984_; lean_object* v_initHeartbeats_4985_; lean_object* v_maxHeartbeats_4986_; lean_object* v_quotContext_4987_; lean_object* v_currMacroScope_4988_; lean_object* v_cancelTk_x3f_4989_; uint8_t v_suppressElabErrors_4990_; lean_object* v_inheritedTraceOptions_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5002_; 
v_fileName_4979_ = lean_ctor_get(v___y_4977_, 0);
v_fileMap_4980_ = lean_ctor_get(v___y_4977_, 1);
v_currRecDepth_4981_ = lean_ctor_get(v___y_4977_, 3);
v_ref_4982_ = lean_ctor_get(v___y_4977_, 5);
v_currNamespace_4983_ = lean_ctor_get(v___y_4977_, 6);
v_openDecls_4984_ = lean_ctor_get(v___y_4977_, 7);
v_initHeartbeats_4985_ = lean_ctor_get(v___y_4977_, 8);
v_maxHeartbeats_4986_ = lean_ctor_get(v___y_4977_, 9);
v_quotContext_4987_ = lean_ctor_get(v___y_4977_, 10);
v_currMacroScope_4988_ = lean_ctor_get(v___y_4977_, 11);
v_cancelTk_x3f_4989_ = lean_ctor_get(v___y_4977_, 12);
v_suppressElabErrors_4990_ = lean_ctor_get_uint8(v___y_4977_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4991_ = lean_ctor_get(v___y_4977_, 13);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___y_4977_);
if (v_isSharedCheck_5002_ == 0)
{
lean_object* v_unused_5003_; lean_object* v_unused_5004_; 
v_unused_5003_ = lean_ctor_get(v___y_4977_, 4);
lean_dec(v_unused_5003_);
v_unused_5004_ = lean_ctor_get(v___y_4977_, 2);
lean_dec(v_unused_5004_);
v___x_4993_ = v___y_4977_;
v_isShared_4994_ = v_isSharedCheck_5002_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_inheritedTraceOptions_4991_);
lean_inc(v_cancelTk_x3f_4989_);
lean_inc(v_currMacroScope_4988_);
lean_inc(v_quotContext_4987_);
lean_inc(v_maxHeartbeats_4986_);
lean_inc(v_initHeartbeats_4985_);
lean_inc(v_openDecls_4984_);
lean_inc(v_currNamespace_4983_);
lean_inc(v_ref_4982_);
lean_inc(v_currRecDepth_4981_);
lean_inc(v_fileMap_4980_);
lean_inc(v_fileName_4979_);
lean_dec(v___y_4977_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5002_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4998_; 
v___x_4995_ = l_Lean_maxRecDepth;
v___x_4996_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v___y_4973_, v___x_4995_);
lean_inc_ref(v___y_4973_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 4, v___x_4996_);
lean_ctor_set(v___x_4993_, 2, v___y_4973_);
v___x_4998_ = v___x_4993_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_fileName_4979_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_fileMap_4980_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v___y_4973_);
lean_ctor_set(v_reuseFailAlloc_5001_, 3, v_currRecDepth_4981_);
lean_ctor_set(v_reuseFailAlloc_5001_, 4, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_5001_, 5, v_ref_4982_);
lean_ctor_set(v_reuseFailAlloc_5001_, 6, v_currNamespace_4983_);
lean_ctor_set(v_reuseFailAlloc_5001_, 7, v_openDecls_4984_);
lean_ctor_set(v_reuseFailAlloc_5001_, 8, v_initHeartbeats_4985_);
lean_ctor_set(v_reuseFailAlloc_5001_, 9, v_maxHeartbeats_4986_);
lean_ctor_set(v_reuseFailAlloc_5001_, 10, v_quotContext_4987_);
lean_ctor_set(v_reuseFailAlloc_5001_, 11, v_currMacroScope_4988_);
lean_ctor_set(v_reuseFailAlloc_5001_, 12, v_cancelTk_x3f_4989_);
lean_ctor_set(v_reuseFailAlloc_5001_, 13, v_inheritedTraceOptions_4991_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*14 + 1, v_suppressElabErrors_4990_);
v___x_4998_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_ctor_set_uint8(v___x_4998_, sizeof(void*)*14, v___y_4975_);
if (v___y_4974_ == 0)
{
v___y_4949_ = v___y_4973_;
v_e_4950_ = v_a_4967_;
v___y_4951_ = v___y_4972_;
v___y_4952_ = v___y_4976_;
v___y_4953_ = v___x_4998_;
v___y_4954_ = v___y_4978_;
goto v___jp_4948_;
}
else
{
lean_object* v___x_4999_; lean_object* v_a_5000_; 
v___x_4999_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_a_4967_, v___y_4976_);
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref(v___x_4999_);
v___y_4949_ = v___y_4973_;
v_e_4950_ = v_a_5000_;
v___y_4951_ = v___y_4972_;
v___y_4952_ = v___y_4976_;
v___y_4953_ = v___x_4998_;
v___y_4954_ = v___y_4978_;
goto v___jp_4948_;
}
}
}
}
v___jp_5005_:
{
if (v___y_5013_ == 0)
{
lean_object* v___x_5014_; lean_object* v_env_5015_; lean_object* v_nextMacroScope_5016_; lean_object* v_ngen_5017_; lean_object* v_auxDeclNGen_5018_; lean_object* v_traceState_5019_; lean_object* v_messages_5020_; lean_object* v_infoState_5021_; lean_object* v_snapshotTasks_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5032_; 
v___x_5014_ = lean_st_ref_take(v___y_5012_);
v_env_5015_ = lean_ctor_get(v___x_5014_, 0);
v_nextMacroScope_5016_ = lean_ctor_get(v___x_5014_, 1);
v_ngen_5017_ = lean_ctor_get(v___x_5014_, 2);
v_auxDeclNGen_5018_ = lean_ctor_get(v___x_5014_, 3);
v_traceState_5019_ = lean_ctor_get(v___x_5014_, 4);
v_messages_5020_ = lean_ctor_get(v___x_5014_, 6);
v_infoState_5021_ = lean_ctor_get(v___x_5014_, 7);
v_snapshotTasks_5022_ = lean_ctor_get(v___x_5014_, 8);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v___x_5014_, 5);
lean_dec(v_unused_5033_);
v___x_5024_ = v___x_5014_;
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_snapshotTasks_5022_);
lean_inc(v_infoState_5021_);
lean_inc(v_messages_5020_);
lean_inc(v_traceState_5019_);
lean_inc(v_auxDeclNGen_5018_);
lean_inc(v_ngen_5017_);
lean_inc(v_nextMacroScope_5016_);
lean_inc(v_env_5015_);
lean_dec(v___x_5014_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
v___x_5026_ = l_Lean_Kernel_enableDiag(v_env_5015_, v___y_5010_);
v___x_5027_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2__spec__0_spec__0___closed__5);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 5, v___x_5027_);
lean_ctor_set(v___x_5024_, 0, v___x_5026_);
v___x_5029_ = v___x_5024_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5026_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_nextMacroScope_5016_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_ngen_5017_);
lean_ctor_set(v_reuseFailAlloc_5031_, 3, v_auxDeclNGen_5018_);
lean_ctor_set(v_reuseFailAlloc_5031_, 4, v_traceState_5019_);
lean_ctor_set(v_reuseFailAlloc_5031_, 5, v___x_5027_);
lean_ctor_set(v_reuseFailAlloc_5031_, 6, v_messages_5020_);
lean_ctor_set(v_reuseFailAlloc_5031_, 7, v_infoState_5021_);
lean_ctor_set(v_reuseFailAlloc_5031_, 8, v_snapshotTasks_5022_);
v___x_5029_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5030_; 
v___x_5030_ = lean_st_ref_set(v___y_5012_, v___x_5029_);
v___y_4972_ = v___y_5007_;
v___y_4973_ = v___y_5006_;
v___y_4974_ = v___y_5008_;
v___y_4975_ = v___y_5010_;
v___y_4976_ = v___y_5011_;
v___y_4977_ = v___y_5009_;
v___y_4978_ = v___y_5012_;
goto v___jp_4971_;
}
}
}
else
{
v___y_4972_ = v___y_5007_;
v___y_4973_ = v___y_5006_;
v___y_4974_ = v___y_5008_;
v___y_4975_ = v___y_5010_;
v___y_4976_ = v___y_5011_;
v___y_4977_ = v___y_5009_;
v___y_4978_ = v___y_5012_;
goto v___jp_4971_;
}
}
v___jp_5034_:
{
lean_object* v___x_5040_; lean_object* v_env_5041_; uint8_t v___x_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; uint8_t v___x_5045_; 
v___x_5040_ = lean_st_ref_get(v___y_5039_);
v_env_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc_ref(v_env_5041_);
lean_dec(v___x_5040_);
v___x_5042_ = l_Lean_getPPInstantiateMVars(v_opts_5035_);
v___x_5043_ = l_Lean_diagnostics;
v___x_5044_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_5035_, v___x_5043_);
v___x_5045_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5041_);
lean_dec_ref(v_env_5041_);
if (v___x_5045_ == 0)
{
if (v___x_5044_ == 0)
{
v___y_4972_ = v___y_5036_;
v___y_4973_ = v_opts_5035_;
v___y_4974_ = v___x_5042_;
v___y_4975_ = v___x_5044_;
v___y_4976_ = v___y_5037_;
v___y_4977_ = v___y_5038_;
v___y_4978_ = v___y_5039_;
goto v___jp_4971_;
}
else
{
v___y_5006_ = v_opts_5035_;
v___y_5007_ = v___y_5036_;
v___y_5008_ = v___x_5042_;
v___y_5009_ = v___y_5038_;
v___y_5010_ = v___x_5044_;
v___y_5011_ = v___y_5037_;
v___y_5012_ = v___y_5039_;
v___y_5013_ = v___x_5045_;
goto v___jp_5005_;
}
}
else
{
v___y_5006_ = v_opts_5035_;
v___y_5007_ = v___y_5036_;
v___y_5008_ = v___x_5042_;
v___y_5009_ = v___y_5038_;
v___y_5010_ = v___x_5044_;
v___y_5011_ = v___y_5037_;
v___y_5012_ = v___y_5039_;
v___y_5013_ = v___x_5044_;
goto v___jp_5005_;
}
}
v___jp_5046_:
{
if (v___y_5053_ == 0)
{
lean_dec_ref(v___y_5050_);
lean_del_object(v___x_4969_);
v_opts_5035_ = v___y_5052_;
v___y_5036_ = v___y_5047_;
v___y_5037_ = v___y_5049_;
v___y_5038_ = v___y_5048_;
v___y_5039_ = v___y_5051_;
goto v___jp_5034_;
}
else
{
lean_object* v___x_5055_; 
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v_a_4967_);
lean_dec_ref(v_delab_4853_);
lean_dec(v_optionsPerPos_4852_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 1);
lean_ctor_set(v___x_4969_, 0, v___y_5050_);
v___x_5055_ = v___x_4969_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___y_5050_);
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
lean_dec_ref(v___y_5058_);
lean_del_object(v___x_4969_);
v_opts_5035_ = v___y_5063_;
v___y_5036_ = v___y_5059_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5062_;
goto v___jp_5034_;
}
else
{
lean_object* v___x_5065_; 
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5060_);
lean_inc(v___y_5061_);
lean_inc_ref(v___y_5059_);
lean_inc(v_a_4967_);
v___x_5065_ = l_Lean_Meta_isProof(v_a_4967_, v___y_5059_, v___y_5061_, v___y_5060_, v___y_5062_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; 
lean_del_object(v___x_4969_);
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref(v___x_5065_);
v___x_5067_ = lean_unbox(v_a_5066_);
if (v___x_5067_ == 0)
{
lean_dec(v_a_5066_);
lean_dec_ref(v___y_5058_);
v_opts_5035_ = v___y_5063_;
v___y_5036_ = v___y_5059_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5062_;
goto v___jp_5034_;
}
else
{
uint8_t v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = lean_unbox(v_a_5066_);
lean_dec(v_a_5066_);
v___x_5069_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v___y_5063_, v___y_5058_, v___x_5068_);
v_opts_5035_ = v___x_5069_;
v___y_5036_ = v___y_5059_;
v___y_5037_ = v___y_5061_;
v___y_5038_ = v___y_5060_;
v___y_5039_ = v___y_5062_;
goto v___jp_5034_;
}
}
else
{
lean_object* v_a_5070_; uint8_t v___x_5071_; 
lean_dec_ref(v___y_5058_);
v_a_5070_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5070_);
lean_dec_ref(v___x_5065_);
v___x_5071_ = l_Lean_Exception_isInterrupt(v_a_5070_);
if (v___x_5071_ == 0)
{
uint8_t v___x_5072_; 
lean_inc(v_a_5070_);
v___x_5072_ = l_Lean_Exception_isRuntime(v_a_5070_);
v___y_5047_ = v___y_5059_;
v___y_5048_ = v___y_5060_;
v___y_5049_ = v___y_5061_;
v___y_5050_ = v_a_5070_;
v___y_5051_ = v___y_5062_;
v___y_5052_ = v___y_5063_;
v___y_5053_ = v___x_5072_;
goto v___jp_5046_;
}
else
{
v___y_5047_ = v___y_5059_;
v___y_5048_ = v___y_5060_;
v___y_5049_ = v___y_5061_;
v___y_5050_ = v_a_5070_;
v___y_5051_ = v___y_5062_;
v___y_5052_ = v___y_5063_;
v___y_5053_ = v___x_5071_;
goto v___jp_5046_;
}
}
}
}
v___jp_5073_:
{
lean_object* v_options_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; uint8_t v___x_5082_; 
v_options_5078_ = lean_ctor_get(v___y_5076_, 2);
lean_inc_ref(v_options_5078_);
v___x_5079_ = l_Lean_pp_proofs;
v___x_5080_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_options_5078_, v___x_5079_);
v___x_5081_ = lean_box(0);
v___x_5082_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5080_, v___x_5081_);
lean_dec(v___x_5080_);
if (v___x_5082_ == 0)
{
v___y_5058_ = v___x_5079_;
v___y_5059_ = v___y_5074_;
v___y_5060_ = v___y_5076_;
v___y_5061_ = v___y_5075_;
v___y_5062_ = v___y_5077_;
v___y_5063_ = v_options_5078_;
v___y_5064_ = v___x_5082_;
goto v___jp_5057_;
}
else
{
uint8_t v___x_5083_; 
v___x_5083_ = l_Lean_Expr_isConst(v_a_4967_);
if (v___x_5083_ == 0)
{
v___y_5058_ = v___x_5079_;
v___y_5059_ = v___y_5074_;
v___y_5060_ = v___y_5076_;
v___y_5061_ = v___y_5075_;
v___y_5062_ = v___y_5077_;
v___y_5063_ = v_options_5078_;
v___y_5064_ = v___x_5082_;
goto v___jp_5057_;
}
else
{
lean_del_object(v___x_4969_);
v_opts_5035_ = v_options_5078_;
v___y_5036_ = v___y_5074_;
v___y_5037_ = v___y_5075_;
v___y_5038_ = v___y_5076_;
v___y_5039_ = v___y_5077_;
goto v___jp_5034_;
}
}
}
v_resetjp_5087_:
{
uint8_t v___x_5090_; 
v___x_5090_ = lean_unbox(v_a_5086_);
lean_dec(v_a_5086_);
if (v___x_5090_ == 0)
{
lean_del_object(v___x_5088_);
v___y_5074_ = v_a_4854_;
v___y_5075_ = v_a_4855_;
v___y_5076_ = v_a_4856_;
v___y_5077_ = v_a_4857_;
goto v___jp_5073_;
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5093_; 
v___x_5091_ = lean_expr_dbg_to_string(v_a_4967_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set_tag(v___x_5088_, 3);
lean_ctor_set(v___x_5088_, 0, v___x_5091_);
v___x_5093_ = v___x_5088_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5094_ = l_Lean_MessageData_ofFormat(v___x_5093_);
v___x_5095_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__8(v___x_5084_, v___x_5094_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_dec_ref(v___x_5095_);
v___y_5074_ = v_a_4854_;
v___y_5075_ = v_a_4855_;
v___y_5076_ = v_a_4856_;
v___y_5077_ = v_a_4857_;
goto v___jp_5073_;
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_del_object(v___x_4969_);
lean_dec(v_a_4967_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec_ref(v_delab_4853_);
lean_dec(v_optionsPerPos_4852_);
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
}
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec_ref(v_delab_4853_);
lean_dec(v_optionsPerPos_4852_);
v_a_5107_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_4966_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_4966_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
v___jp_4859_:
{
lean_object* v_infos_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v_infos_4862_ = lean_ctor_get(v_snd_4861_, 1);
lean_inc(v_infos_4862_);
lean_dec_ref(v_snd_4861_);
v___x_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4863_, 0, v_fst_4860_);
lean_ctor_set(v___x_4863_, 1, v_infos_4862_);
v___x_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
return v___x_4864_;
}
v___jp_4865_:
{
if (v___y_4872_ == 0)
{
if (lean_obj_tag(v___y_4871_) == 0)
{
lean_object* v___x_4873_; 
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
v___x_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___y_4871_);
return v___x_4873_;
}
else
{
lean_object* v_id_4874_; uint8_t v___x_4875_; 
v_id_4874_ = lean_ctor_get(v___y_4871_, 0);
v___x_4875_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4870_, v_id_4874_);
lean_dec(v___y_4870_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; 
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
v___x_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___y_4871_);
return v___x_4876_;
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec_ref(v___y_4871_);
v___x_4877_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4878_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4877_, v___y_4869_, v___y_4868_, v___y_4867_, v___y_4866_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v_fst_4880_; lean_object* v_snd_4881_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref(v___x_4878_);
v_fst_4880_ = lean_ctor_get(v_a_4879_, 0);
lean_inc(v_fst_4880_);
v_snd_4881_ = lean_ctor_get(v_a_4879_, 1);
lean_inc(v_snd_4881_);
lean_dec(v_a_4879_);
v_fst_4860_ = v_fst_4880_;
v_snd_4861_ = v_snd_4881_;
goto v___jp_4859_;
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4878_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4878_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
else
{
lean_object* v___x_4890_; 
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
v___x_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___y_4871_);
return v___x_4890_;
}
}
v___jp_4891_:
{
lean_object* v_fileName_4899_; lean_object* v_fileMap_4900_; lean_object* v_options_4901_; lean_object* v_currRecDepth_4902_; lean_object* v_maxRecDepth_4903_; lean_object* v_currNamespace_4904_; lean_object* v_openDecls_4905_; lean_object* v_initHeartbeats_4906_; lean_object* v_maxHeartbeats_4907_; lean_object* v_quotContext_4908_; lean_object* v_currMacroScope_4909_; uint8_t v_diag_4910_; lean_object* v_cancelTk_x3f_4911_; uint8_t v_suppressElabErrors_4912_; lean_object* v_inheritedTraceOptions_4913_; uint8_t v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v_fileName_4899_ = lean_ctor_get(v___y_4897_, 0);
v_fileMap_4900_ = lean_ctor_get(v___y_4897_, 1);
v_options_4901_ = lean_ctor_get(v___y_4897_, 2);
v_currRecDepth_4902_ = lean_ctor_get(v___y_4897_, 3);
v_maxRecDepth_4903_ = lean_ctor_get(v___y_4897_, 4);
v_currNamespace_4904_ = lean_ctor_get(v___y_4897_, 6);
v_openDecls_4905_ = lean_ctor_get(v___y_4897_, 7);
v_initHeartbeats_4906_ = lean_ctor_get(v___y_4897_, 8);
v_maxHeartbeats_4907_ = lean_ctor_get(v___y_4897_, 9);
v_quotContext_4908_ = lean_ctor_get(v___y_4897_, 10);
v_currMacroScope_4909_ = lean_ctor_get(v___y_4897_, 11);
v_diag_4910_ = lean_ctor_get_uint8(v___y_4897_, sizeof(void*)*14);
v_cancelTk_x3f_4911_ = lean_ctor_get(v___y_4897_, 12);
v_suppressElabErrors_4912_ = lean_ctor_get_uint8(v___y_4897_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4913_ = lean_ctor_get(v___y_4897_, 13);
v___x_4914_ = l_Lean_Options_getInPattern(v___y_4892_);
lean_dec_ref(v___y_4892_);
v___x_4915_ = l_Lean_SubExpr_mkRoot(v___y_4893_);
v___x_4916_ = lean_unsigned_to_nat(0u);
lean_inc(v_openDecls_4905_);
lean_inc(v_currNamespace_4904_);
v___x_4917_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4917_, 0, v_optionsPerPos_4894_);
lean_ctor_set(v___x_4917_, 1, v_currNamespace_4904_);
lean_ctor_set(v___x_4917_, 2, v_openDecls_4905_);
lean_ctor_set(v___x_4917_, 3, v___x_4915_);
lean_ctor_set(v___x_4917_, 4, v___x_4916_);
lean_ctor_set_uint8(v___x_4917_, sizeof(void*)*5, v___x_4914_);
v___x_4918_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4919_ = lean_st_mk_ref(v___x_4918_);
v___x_4920_ = lean_box(0);
lean_inc_ref(v_inheritedTraceOptions_4913_);
lean_inc(v_cancelTk_x3f_4911_);
lean_inc(v_currMacroScope_4909_);
lean_inc(v_quotContext_4908_);
lean_inc(v_maxHeartbeats_4907_);
lean_inc(v_initHeartbeats_4906_);
lean_inc(v_openDecls_4905_);
lean_inc(v_currNamespace_4904_);
lean_inc(v_maxRecDepth_4903_);
lean_inc(v_currRecDepth_4902_);
lean_inc_ref(v_options_4901_);
lean_inc_ref(v_fileMap_4900_);
lean_inc_ref(v_fileName_4899_);
v___x_4921_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4921_, 0, v_fileName_4899_);
lean_ctor_set(v___x_4921_, 1, v_fileMap_4900_);
lean_ctor_set(v___x_4921_, 2, v_options_4901_);
lean_ctor_set(v___x_4921_, 3, v_currRecDepth_4902_);
lean_ctor_set(v___x_4921_, 4, v_maxRecDepth_4903_);
lean_ctor_set(v___x_4921_, 5, v___x_4920_);
lean_ctor_set(v___x_4921_, 6, v_currNamespace_4904_);
lean_ctor_set(v___x_4921_, 7, v_openDecls_4905_);
lean_ctor_set(v___x_4921_, 8, v_initHeartbeats_4906_);
lean_ctor_set(v___x_4921_, 9, v_maxHeartbeats_4907_);
lean_ctor_set(v___x_4921_, 10, v_quotContext_4908_);
lean_ctor_set(v___x_4921_, 11, v_currMacroScope_4909_);
lean_ctor_set(v___x_4921_, 12, v_cancelTk_x3f_4911_);
lean_ctor_set(v___x_4921_, 13, v_inheritedTraceOptions_4913_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*14, v_diag_4910_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*14 + 1, v_suppressElabErrors_4912_);
lean_inc(v___y_4898_);
lean_inc(v___y_4896_);
lean_inc_ref(v___y_4895_);
lean_inc(v___x_4919_);
v___x_4922_ = lean_apply_7(v_delab_4853_, v___x_4917_, v___x_4919_, v___y_4895_, v___y_4896_, v___x_4921_, v___y_4898_, lean_box(0));
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; 
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref(v___x_4922_);
v___x_4924_ = lean_st_ref_get(v___x_4919_);
lean_dec(v___x_4919_);
v_fst_4860_ = v_a_4923_;
v_snd_4861_ = v___x_4924_;
goto v___jp_4859_;
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
lean_dec(v___x_4919_);
v_a_4925_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4925_);
lean_dec_ref(v___x_4922_);
v___x_4926_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4927_ = l_Lean_Exception_isInterrupt(v_a_4925_);
if (v___x_4927_ == 0)
{
uint8_t v___x_4928_; 
lean_inc(v_a_4925_);
v___x_4928_ = l_Lean_Exception_isRuntime(v_a_4925_);
v___y_4866_ = v___y_4898_;
v___y_4867_ = v___y_4897_;
v___y_4868_ = v___y_4896_;
v___y_4869_ = v___y_4895_;
v___y_4870_ = v___x_4926_;
v___y_4871_ = v_a_4925_;
v___y_4872_ = v___x_4928_;
goto v___jp_4865_;
}
else
{
v___y_4866_ = v___y_4898_;
v___y_4867_ = v___y_4897_;
v___y_4868_ = v___y_4896_;
v___y_4869_ = v___y_4895_;
v___y_4870_ = v___x_4926_;
v___y_4871_ = v_a_4925_;
v___y_4872_ = v___x_4927_;
goto v___jp_4865_;
}
}
}
v___jp_4929_:
{
uint8_t v___x_4936_; 
v___x_4936_ = l_Lean_getPPAll(v___y_4930_);
if (v___x_4936_ == 0)
{
uint8_t v___x_4937_; 
v___x_4937_ = l_Lean_getPPAnalyze(v___y_4930_);
if (v___x_4937_ == 0)
{
v___y_4892_ = v___y_4930_;
v___y_4893_ = v_e_4931_;
v_optionsPerPos_4894_ = v_optionsPerPos_4852_;
v___y_4895_ = v___y_4932_;
v___y_4896_ = v___y_4933_;
v___y_4897_ = v___y_4934_;
v___y_4898_ = v___y_4935_;
goto v___jp_4891_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4852_) == 0)
{
v___y_4892_ = v___y_4930_;
v___y_4893_ = v_e_4931_;
v_optionsPerPos_4894_ = v_optionsPerPos_4852_;
v___y_4895_ = v___y_4932_;
v___y_4896_ = v___y_4933_;
v___y_4897_ = v___y_4934_;
v___y_4898_ = v___y_4935_;
goto v___jp_4891_;
}
else
{
lean_object* v___x_4938_; 
lean_inc(v___y_4935_);
lean_inc_ref(v___y_4934_);
lean_inc(v___y_4933_);
lean_inc_ref(v___y_4932_);
lean_inc_ref(v_e_4931_);
v___x_4938_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref(v___x_4938_);
v___y_4892_ = v___y_4930_;
v___y_4893_ = v_e_4931_;
v_optionsPerPos_4894_ = v_a_4939_;
v___y_4895_ = v___y_4932_;
v___y_4896_ = v___y_4933_;
v___y_4897_ = v___y_4934_;
v___y_4898_ = v___y_4935_;
goto v___jp_4891_;
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec_ref(v_e_4931_);
lean_dec_ref(v___y_4930_);
lean_dec_ref(v_delab_4853_);
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
else
{
v___y_4892_ = v___y_4930_;
v___y_4893_ = v_e_4931_;
v_optionsPerPos_4894_ = v_optionsPerPos_4852_;
v___y_4895_ = v___y_4932_;
v___y_4896_ = v___y_4933_;
v___y_4897_ = v___y_4934_;
v___y_4898_ = v___y_4935_;
goto v___jp_4891_;
}
}
v___jp_4948_:
{
uint8_t v___x_4955_; 
v___x_4955_ = l_Lean_getPPBeta(v___y_4949_);
if (v___x_4955_ == 0)
{
v___y_4930_ = v___y_4949_;
v_e_4931_ = v_e_4950_;
v___y_4932_ = v___y_4951_;
v___y_4933_ = v___y_4952_;
v___y_4934_ = v___y_4953_;
v___y_4935_ = v___y_4954_;
goto v___jp_4929_;
}
else
{
lean_object* v___x_4956_; 
lean_inc(v___y_4954_);
lean_inc_ref(v___y_4953_);
v___x_4956_ = l_Lean_Core_betaReduce(v_e_4950_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref(v___x_4956_);
v___y_4930_ = v___y_4949_;
v_e_4931_ = v_a_4957_;
v___y_4932_ = v___y_4951_;
v___y_4933_ = v___y_4952_;
v___y_4934_ = v___y_4953_;
v___y_4935_ = v___y_4954_;
goto v___jp_4929_;
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec_ref(v___y_4949_);
lean_dec_ref(v_delab_4853_);
lean_dec(v_optionsPerPos_4852_);
v_a_4958_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4956_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4956_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5115_, lean_object* v_optionsPerPos_5116_, lean_object* v_delab_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5115_, v_optionsPerPos_5116_, v_delab_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5124_, lean_object* v_e_5125_, lean_object* v_optionsPerPos_5126_, lean_object* v_delab_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v___x_5133_; 
v___x_5133_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5125_, v_optionsPerPos_5126_, v_delab_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5134_, lean_object* v_e_5135_, lean_object* v_optionsPerPos_5136_, lean_object* v_delab_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5134_, v_e_5135_, v_optionsPerPos_5136_, v_delab_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5145_, lean_object* v_optionsPerPos_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5153_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5145_, v_optionsPerPos_5146_, v___x_5152_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5162_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5156_ = v___x_5153_;
v_isShared_5157_ = v_isSharedCheck_5162_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5153_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5162_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v_fst_5158_; lean_object* v___x_5160_; 
v_fst_5158_ = lean_ctor_get(v_a_5154_, 0);
lean_inc(v_fst_5158_);
lean_dec(v_a_5154_);
if (v_isShared_5157_ == 0)
{
lean_ctor_set(v___x_5156_, 0, v_fst_5158_);
v___x_5160_ = v___x_5156_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_fst_5158_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
v_a_5163_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5153_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5153_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5171_, lean_object* v_optionsPerPos_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_PrettyPrinter_delab(v_e_5171_, v_optionsPerPos_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5243_; uint8_t v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5243_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5244_ = 0;
v___x_5245_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5246_ = l_Lean_registerTraceClass(v___x_5243_, v___x_5244_, v___x_5245_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
lean_dec_ref(v___x_5246_);
v___x_5247_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5248_ = l_Lean_registerTraceClass(v___x_5247_, v___x_5244_, v___x_5245_);
return v___x_5248_;
}
else
{
return v___x_5246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5250_;
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
res = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabFailureId);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM);
res = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_1489834770____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabAttribute);
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute);
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
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
