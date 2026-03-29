// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Basic
// Imports: public import Lean.Elab.Tactic.Simp public import Lean.Elab.Tactic.Do.Attr import Init.Omega
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 186, 72, 71, 180, 239, 13, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 197, 164, 82, 155, 28, 143, 213)}};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "disable `mvcgen` usage warning"};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(217, 19, 39, 228, 182, 81, 226, 63)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 41, 69, 108, 13, 191, 254, 76)}};
static const lean_object* l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3;
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
static const lean_array_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 120, 209, 69, 128, 204, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 87, 81, 188, 35, 250, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26_value;
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
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_value;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "adding "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(lean_object* v_name_123_, lean_object* v_decl_124_, lean_object* v_ref_125_){
_start:
{
lean_object* v_defValue_127_; lean_object* v_descr_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_155_; 
v_defValue_127_ = lean_ctor_get(v_decl_124_, 0);
v_descr_128_ = lean_ctor_get(v_decl_124_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_decl_124_);
if (v_isSharedCheck_155_ == 0)
{
v___x_130_ = v_decl_124_;
v_isShared_131_ = v_isSharedCheck_155_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_descr_128_);
lean_inc(v_defValue_127_);
lean_dec(v_decl_124_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_155_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_alloc_ctor(1, 0, 1);
v___x_133_ = lean_unbox(v_defValue_127_);
lean_ctor_set_uint8(v___x_132_, 0, v___x_133_);
lean_inc_n(v_name_123_, 2);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_name_123_);
lean_ctor_set(v___x_134_, 1, v_ref_125_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
lean_ctor_set(v___x_134_, 3, v_descr_128_);
v___x_135_ = lean_register_option(v_name_123_, v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_145_; 
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_146_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_defValue_127_);
lean_ctor_set(v___x_130_, 0, v_name_123_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_name_123_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_defValue_127_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_del_object(v___x_130_);
lean_dec(v_defValue_127_);
lean_dec(v_name_123_);
v_a_147_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_135_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_135_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_156_, lean_object* v_decl_157_, lean_object* v_ref_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(v_name_156_, v_decl_157_, v_ref_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_180_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_181_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_182_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(v___x_179_, v___x_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4____boxed(lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx(lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(1u);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___boxed(lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_Tactic_Do_Fuel_ctorIdx(v_x_188_);
lean_dec(v_x_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(lean_object* v_t_190_, lean_object* v_k_191_){
_start:
{
if (lean_obj_tag(v_t_190_) == 0)
{
lean_object* v_n_192_; lean_object* v___x_193_; 
v_n_192_ = lean_ctor_get(v_t_190_, 0);
lean_inc(v_n_192_);
lean_dec_ref(v_t_190_);
v___x_193_ = lean_apply_1(v_k_191_, v_n_192_);
return v___x_193_;
}
else
{
return v_k_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim(lean_object* v_motive_194_, lean_object* v_ctorIdx_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_k_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_196_, v_k_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___boxed(lean_object* v_motive_200_, lean_object* v_ctorIdx_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_k_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim(v_motive_200_, v_ctorIdx_201_, v_t_202_, v_h_203_, v_k_204_);
lean_dec(v_ctorIdx_201_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim___redArg(lean_object* v_t_206_, lean_object* v_limited_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_206_, v_limited_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim(lean_object* v_motive_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_limited_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_210_, v_limited_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim___redArg(lean_object* v_t_214_, lean_object* v_unlimited_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_214_, v_unlimited_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim(lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_unlimited_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_218_, v_unlimited_220_);
return v___x_221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v_n_224_; uint8_t v___x_225_; 
v_n_224_ = lean_ctor_get(v_x_222_, 0);
v___x_225_ = 0;
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_n_226_; uint8_t v___x_227_; 
v_n_226_ = lean_ctor_get(v_x_223_, 0);
v___x_227_ = lean_nat_dec_eq(v_n_224_, v_n_226_);
if (v___x_227_ == 0)
{
return v___x_225_;
}
else
{
return v___x_227_;
}
}
else
{
return v___x_225_;
}
}
else
{
if (lean_obj_tag(v_x_223_) == 0)
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 1;
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_230_, v_x_231_);
lean_dec(v_x_231_);
lean_dec(v_x_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_234_, v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel___boxed(lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel(v_x_237_, v_x_238_);
lean_dec(v_x_238_);
lean_dec(v_x_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_));
v___x_256_ = 0;
v___x_257_ = 1;
v___x_258_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_255_, v_e_249_, v___x_256_, v___x_257_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3____boxed(lean_object* v_e_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(v_e_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(v_e_266_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_evalUnsafe_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3____boxed(lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_Do_evalUnsafe_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(lean_object* v_msgData_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; lean_object* v_mctx_293_; lean_object* v_lctx_294_; lean_object* v_options_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_290_ = lean_st_ref_get(v___y_288_);
v_env_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_env_291_);
lean_dec(v___x_290_);
v___x_292_ = lean_st_ref_get(v___y_286_);
v_mctx_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_293_);
lean_dec(v___x_292_);
v_lctx_294_ = lean_ctor_get(v___y_285_, 2);
v_options_295_ = lean_ctor_get(v___y_287_, 2);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_lctx_294_);
v___x_296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_296_, 0, v_env_291_);
lean_ctor_set(v___x_296_, 1, v_mctx_293_);
lean_ctor_set(v___x_296_, 2, v_lctx_294_);
lean_ctor_set(v___x_296_, 3, v_options_295_);
v___x_297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_msgData_284_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4___boxed(lean_object* v_msgData_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(v_msgData_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_box(1);
v___x_307_ = l_Lean_MessageData_ofFormat(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__2));
v___x_312_ = l_Lean_MessageData_ofFormat(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
return v_x_313_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_338_; 
v_head_315_ = lean_ctor_get(v_x_314_, 0);
v_tail_316_ = lean_ctor_get(v_x_314_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_338_ == 0)
{
v___x_318_ = v_x_314_;
v_isShared_319_ = v_isSharedCheck_338_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_tail_316_);
lean_inc(v_head_315_);
lean_dec(v_x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_338_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_before_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_336_; 
v_before_320_ = lean_ctor_get(v_head_315_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_head_315_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_head_315_, 1);
lean_dec(v_unused_337_);
v___x_322_ = v_head_315_;
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_before_320_);
lean_dec(v_head_315_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 7);
lean_ctor_set(v___x_322_, 1, v___x_324_);
lean_ctor_set(v___x_322_, 0, v_x_313_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_x_313_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_335_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__3);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 7);
lean_ctor_set(v___x_318_, 1, v___x_327_);
lean_ctor_set(v___x_318_, 0, v___x_326_);
v___x_329_ = v___x_318_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_334_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = l_Lean_MessageData_ofSyntax(v_before_320_);
v___x_331_ = l_Lean_indentD(v___x_330_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v_x_313_ = v___x_332_;
v_x_314_ = v_tail_316_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9(lean_object* v_opts_339_, lean_object* v_opt_340_){
_start:
{
lean_object* v_name_341_; lean_object* v_defValue_342_; lean_object* v_map_343_; lean_object* v___x_344_; 
v_name_341_ = lean_ctor_get(v_opt_340_, 0);
v_defValue_342_ = lean_ctor_get(v_opt_340_, 1);
v_map_343_ = lean_ctor_get(v_opts_339_, 0);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_343_, v_name_341_);
if (lean_obj_tag(v___x_344_) == 0)
{
uint8_t v___x_345_; 
v___x_345_ = lean_unbox(v_defValue_342_);
return v___x_345_;
}
else
{
lean_object* v_val_346_; 
v_val_346_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_346_);
lean_dec_ref(v___x_344_);
if (lean_obj_tag(v_val_346_) == 1)
{
uint8_t v_v_347_; 
v_v_347_ = lean_ctor_get_uint8(v_val_346_, 0);
lean_dec_ref(v_val_346_);
return v_v_347_;
}
else
{
uint8_t v___x_348_; 
lean_dec(v_val_346_);
v___x_348_ = lean_unbox(v_defValue_342_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_349_, lean_object* v_opt_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9(v_opts_349_, v_opt_350_);
lean_dec_ref(v_opt_350_);
lean_dec_ref(v_opts_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__1));
v___x_357_ = l_Lean_MessageData_ofFormat(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg(lean_object* v_msgData_358_, lean_object* v_macroStack_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_options_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_options_362_ = lean_ctor_get(v___y_360_, 2);
v___x_363_ = l_Lean_Elab_pp_macroStack;
v___x_364_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__9(v_options_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v_macroStack_359_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_msgData_358_);
return v___x_365_;
}
else
{
if (lean_obj_tag(v_macroStack_359_) == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_358_);
return v___x_366_;
}
else
{
lean_object* v_head_367_; lean_object* v_after_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_383_; 
v_head_367_ = lean_ctor_get(v_macroStack_359_, 0);
lean_inc(v_head_367_);
v_after_368_ = lean_ctor_get(v_head_367_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_head_367_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_head_367_, 0);
lean_dec(v_unused_384_);
v___x_370_ = v_head_367_;
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_after_368_);
lean_dec(v_head_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10___closed__0);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 7);
lean_ctor_set(v___x_370_, 1, v___x_372_);
lean_ctor_set(v___x_370_, 0, v_msgData_358_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_msgData_358_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_msgData_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_375_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___closed__2);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_MessageData_ofSyntax(v_after_368_);
v___x_378_ = l_Lean_indentD(v___x_377_);
v_msgData_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_379_, 0, v___x_376_);
lean_ctor_set(v_msgData_379_, 1, v___x_378_);
v___x_380_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5_spec__10(v_msgData_379_, v_macroStack_359_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg___boxed(lean_object* v_msgData_385_, lean_object* v_macroStack_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg(v_msgData_385_, v_macroStack_386_, v___y_387_);
lean_dec_ref(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_ref_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v_macroStack_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_ref_398_ = lean_ctor_get(v___y_395_, 5);
v___x_399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(v_msg_390_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
v_macroStack_401_ = lean_ctor_get(v___y_391_, 1);
lean_inc_n(v_macroStack_401_, 2);
v___x_402_ = l_Lean_Elab_getBetterRef(v_ref_398_, v_macroStack_401_);
v___x_403_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg(v_a_400_, v_macroStack_401_, v___y_395_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_402_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v_key_425_; lean_object* v_value_426_; lean_object* v_tail_427_; uint8_t v___x_428_; 
v_key_425_ = lean_ctor_get(v_x_423_, 0);
v_value_426_ = lean_ctor_get(v_x_423_, 1);
v_tail_427_ = lean_ctor_get(v_x_423_, 2);
v___x_428_ = lean_name_eq(v_key_425_, v_a_422_);
if (v___x_428_ == 0)
{
v_x_423_ = v_tail_427_;
goto _start;
}
else
{
lean_object* v___x_430_; 
lean_inc(v_value_426_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v_value_426_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg(v_a_431_, v_x_432_);
lean_dec(v_x_432_);
lean_dec(v_a_431_);
return v_res_433_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_434_; uint64_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1723u);
v___x_435_ = lean_uint64_of_nat(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg(lean_object* v_m_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_buckets_438_; lean_object* v___x_439_; uint64_t v___y_441_; 
v_buckets_438_ = lean_ctor_get(v_m_436_, 1);
v___x_439_ = lean_array_get_size(v_buckets_438_);
if (lean_obj_tag(v_a_437_) == 0)
{
uint64_t v___x_455_; 
v___x_455_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___closed__0);
v___y_441_ = v___x_455_;
goto v___jp_440_;
}
else
{
uint64_t v_hash_456_; 
v_hash_456_ = lean_ctor_get_uint64(v_a_437_, sizeof(void*)*2);
v___y_441_ = v_hash_456_;
goto v___jp_440_;
}
v___jp_440_:
{
uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v_fold_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_442_ = 32ULL;
v___x_443_ = lean_uint64_shift_right(v___y_441_, v___x_442_);
v_fold_444_ = lean_uint64_xor(v___y_441_, v___x_443_);
v___x_445_ = 16ULL;
v___x_446_ = lean_uint64_shift_right(v_fold_444_, v___x_445_);
v___x_447_ = lean_uint64_xor(v_fold_444_, v___x_446_);
v___x_448_ = lean_uint64_to_usize(v___x_447_);
v___x_449_ = lean_usize_of_nat(v___x_439_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_sub(v___x_449_, v___x_450_);
v___x_452_ = lean_usize_land(v___x_448_, v___x_451_);
v___x_453_ = lean_array_uget_borrowed(v_buckets_438_, v___x_452_);
v___x_454_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg(v_a_437_, v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg(v_m_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_m_457_);
return v_res_459_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_460_; double v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_float_of_nat(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_465_, lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_ref_472_; lean_object* v___x_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_518_; 
v_ref_472_ = lean_ctor_get(v___y_469_, 5);
v___x_473_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(v_msg_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_518_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_518_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_518_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v_traceState_479_; lean_object* v_env_480_; lean_object* v_nextMacroScope_481_; lean_object* v_ngen_482_; lean_object* v_auxDeclNGen_483_; lean_object* v_cache_484_; lean_object* v_messages_485_; lean_object* v_infoState_486_; lean_object* v_snapshotTasks_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_517_; 
v___x_478_ = lean_st_ref_take(v___y_470_);
v_traceState_479_ = lean_ctor_get(v___x_478_, 4);
v_env_480_ = lean_ctor_get(v___x_478_, 0);
v_nextMacroScope_481_ = lean_ctor_get(v___x_478_, 1);
v_ngen_482_ = lean_ctor_get(v___x_478_, 2);
v_auxDeclNGen_483_ = lean_ctor_get(v___x_478_, 3);
v_cache_484_ = lean_ctor_get(v___x_478_, 5);
v_messages_485_ = lean_ctor_get(v___x_478_, 6);
v_infoState_486_ = lean_ctor_get(v___x_478_, 7);
v_snapshotTasks_487_ = lean_ctor_get(v___x_478_, 8);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_517_ == 0)
{
v___x_489_ = v___x_478_;
v_isShared_490_ = v_isSharedCheck_517_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snapshotTasks_487_);
lean_inc(v_infoState_486_);
lean_inc(v_messages_485_);
lean_inc(v_cache_484_);
lean_inc(v_traceState_479_);
lean_inc(v_auxDeclNGen_483_);
lean_inc(v_ngen_482_);
lean_inc(v_nextMacroScope_481_);
lean_inc(v_env_480_);
lean_dec(v___x_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_517_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint64_t v_tid_491_; lean_object* v_traces_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_516_; 
v_tid_491_ = lean_ctor_get_uint64(v_traceState_479_, sizeof(void*)*1);
v_traces_492_ = lean_ctor_get(v_traceState_479_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_traceState_479_);
if (v_isSharedCheck_516_ == 0)
{
v___x_494_ = v_traceState_479_;
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_traces_492_);
lean_dec(v_traceState_479_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; double v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_498_ = 0;
v___x_499_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_500_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_500_, 0, v_cls_465_);
lean_ctor_set(v___x_500_, 1, v___x_496_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3, v___x_497_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3 + 8, v___x_497_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*3 + 16, v___x_498_);
v___x_501_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_502_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v_a_474_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
lean_inc(v_ref_472_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_472_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_PersistentArray_push___redArg(v_traces_492_, v___x_503_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_504_);
v___x_506_ = v___x_494_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_504_);
lean_ctor_set_uint64(v_reuseFailAlloc_515_, sizeof(void*)*1, v_tid_491_);
v___x_506_ = v_reuseFailAlloc_515_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v___x_506_);
v___x_508_ = v___x_489_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_env_480_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_nextMacroScope_481_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_ngen_482_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_auxDeclNGen_483_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_cache_484_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_messages_485_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_infoState_486_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v_snapshotTasks_487_);
v___x_508_ = v_reuseFailAlloc_514_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_509_ = lean_st_ref_set(v___y_470_, v___x_508_);
v___x_510_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_510_);
v___x_512_ = v___x_476_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg(v_cls_519_, v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(lean_object* v_keys_527_, lean_object* v_i_528_, lean_object* v_k_529_){
_start:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_array_get_size(v_keys_527_);
v___x_531_ = lean_nat_dec_lt(v_i_528_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec(v_i_528_);
return v___x_531_;
}
else
{
lean_object* v_k_x27_532_; uint8_t v___x_533_; 
v_k_x27_532_ = lean_array_fget_borrowed(v_keys_527_, v_i_528_);
v___x_533_ = l_Lean_instBEqExtraModUse_beq(v_k_529_, v_k_x27_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_i_528_, v___x_534_);
lean_dec(v_i_528_);
v_i_528_ = v___x_535_;
goto _start;
}
else
{
lean_dec(v_i_528_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_keys_537_, lean_object* v_i_538_, lean_object* v_k_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_keys_537_, v_i_538_, v_k_539_);
lean_dec_ref(v_k_539_);
lean_dec_ref(v_keys_537_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; 
v___x_542_ = ((size_t)5ULL);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_shift_left(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; 
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_547_ = lean_usize_sub(v___x_546_, v___x_545_);
return v___x_547_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_548_, size_t v_x_549_, lean_object* v_x_550_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_object* v_es_551_; lean_object* v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_j_556_; lean_object* v___x_557_; 
v_es_551_ = lean_ctor_get(v_x_548_, 0);
v___x_552_ = lean_box(2);
v___x_553_ = ((size_t)5ULL);
v___x_554_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_555_ = lean_usize_land(v_x_549_, v___x_554_);
v_j_556_ = lean_usize_to_nat(v___x_555_);
v___x_557_ = lean_array_get_borrowed(v___x_552_, v_es_551_, v_j_556_);
lean_dec(v_j_556_);
switch(lean_obj_tag(v___x_557_))
{
case 0:
{
lean_object* v_key_558_; uint8_t v___x_559_; 
v_key_558_ = lean_ctor_get(v___x_557_, 0);
v___x_559_ = l_Lean_instBEqExtraModUse_beq(v_x_550_, v_key_558_);
return v___x_559_;
}
case 1:
{
lean_object* v_node_560_; size_t v___x_561_; 
v_node_560_ = lean_ctor_get(v___x_557_, 0);
v___x_561_ = lean_usize_shift_right(v_x_549_, v___x_553_);
v_x_548_ = v_node_560_;
v_x_549_ = v___x_561_;
goto _start;
}
default: 
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
}
}
else
{
lean_object* v_ks_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_ks_564_ = lean_ctor_get(v_x_548_, 0);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_ks_564_, v___x_565_, v_x_550_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
size_t v_x_12651__boxed_570_; uint8_t v_res_571_; lean_object* v_r_572_; 
v_x_12651__boxed_570_ = lean_unbox_usize(v_x_568_);
lean_dec(v_x_568_);
v_res_571_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_567_, v_x_12651__boxed_570_, v_x_569_);
lean_dec_ref(v_x_569_);
lean_dec_ref(v_x_567_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
uint64_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v___x_575_ = l_Lean_instHashableExtraModUse_hash(v_x_574_);
v___x_576_ = lean_uint64_to_usize(v___x_575_);
v___x_577_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_573_, v___x_576_, v_x_574_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg(v_x_578_, v_x_579_);
lean_dec_ref(v_x_579_);
lean_dec_ref(v_x_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__1));
v___x_585_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__0));
v___x_586_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_587_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__3);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__4);
v___x_593_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_ctor_set(v___x_593_, 3, v___x_592_);
lean_ctor_set(v___x_593_, 4, v___x_592_);
lean_ctor_set(v___x_593_, 5, v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__9));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__11));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_cls_608_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__8));
v___x_609_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__15));
v___x_610_ = l_Lean_Name_append(v___x_609_, v_cls_608_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__17));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__19));
v___x_616_ = l_Lean_stringToMessageData(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0(lean_object* v_mod_621_, uint8_t v_isMeta_622_, lean_object* v_hint_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_env_632_; uint8_t v_isExporting_633_; lean_object* v___x_634_; lean_object* v_env_635_; lean_object* v___x_636_; lean_object* v_entry_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_631_ = lean_st_ref_get(v___y_629_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v_isExporting_633_ = lean_ctor_get_uint8(v_env_632_, sizeof(void*)*8);
lean_dec_ref(v_env_632_);
v___x_634_ = lean_st_ref_get(v___y_629_);
v_env_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_635_);
lean_dec(v___x_634_);
v___x_636_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_621_);
v_entry_637_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_637_, 0, v_mod_621_);
lean_ctor_set_uint8(v_entry_637_, sizeof(void*)*1, v_isExporting_633_);
lean_ctor_set_uint8(v_entry_637_, sizeof(void*)*1 + 1, v_isMeta_622_);
v___x_638_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_639_ = lean_box(1);
v___x_640_ = lean_box(0);
v___x_683_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_636_, v___x_638_, v_env_635_, v___x_639_, v___x_640_);
v___x_684_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg(v___x_683_, v_entry_637_);
lean_dec(v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v_options_685_; uint8_t v_hasTrace_686_; 
v_options_685_ = lean_ctor_get(v___y_628_, 2);
v_hasTrace_686_ = lean_ctor_get_uint8(v_options_685_, sizeof(void*)*1);
if (v_hasTrace_686_ == 0)
{
lean_dec(v_hint_623_);
lean_dec(v_mod_621_);
v___y_642_ = v___y_627_;
v___y_643_ = v___y_629_;
goto v___jp_641_;
}
else
{
lean_object* v_inheritedTraceOptions_687_; lean_object* v_cls_688_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_inheritedTraceOptions_687_ = lean_ctor_get(v___y_628_, 13);
v_cls_688_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__8));
v___x_708_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__16);
v___x_709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_687_, v_options_685_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v_hint_623_);
lean_dec(v_mod_621_);
v___y_642_ = v___y_627_;
v___y_643_ = v___y_629_;
goto v___jp_641_;
}
else
{
lean_object* v___x_710_; lean_object* v___y_712_; 
v___x_710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__18);
if (v_isExporting_633_ == 0)
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__23));
v___y_712_ = v___x_719_;
goto v___jp_711_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__24));
v___y_712_ = v___x_720_;
goto v___jp_711_;
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc_ref(v___y_712_);
v___x_713_ = l_Lean_stringToMessageData(v___y_712_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_710_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
if (v_isMeta_622_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__21));
v___y_695_ = v___x_716_;
v___y_696_ = v___x_717_;
goto v___jp_694_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__22));
v___y_695_ = v___x_716_;
v___y_696_ = v___x_718_;
goto v___jp_694_;
}
}
}
v___jp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___y_690_);
lean_ctor_set(v___x_692_, 1, v___y_691_);
v___x_693_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg(v_cls_688_, v___x_692_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_dec_ref(v___x_693_);
v___y_642_ = v___y_627_;
v___y_643_ = v___y_629_;
goto v___jp_641_;
}
else
{
lean_dec_ref(v_entry_637_);
return v___x_693_;
}
}
v___jp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
lean_inc_ref(v___y_696_);
v___x_697_ = l_Lean_stringToMessageData(v___y_696_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___y_695_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__10);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_MessageData_ofName(v_mod_621_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Lean_Name_isAnonymous(v_hint_623_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__12);
v___x_705_ = l_Lean_MessageData_ofName(v_hint_623_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___y_690_ = v___x_702_;
v___y_691_ = v___x_706_;
goto v___jp_689_;
}
else
{
lean_object* v___x_707_; 
lean_dec(v_hint_623_);
v___x_707_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__13);
v___y_690_ = v___x_702_;
v___y_691_ = v___x_707_;
goto v___jp_689_;
}
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v_entry_637_);
lean_dec(v_hint_623_);
lean_dec(v_mod_621_);
v___x_721_ = lean_box(0);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
v___jp_641_:
{
lean_object* v___x_644_; lean_object* v_toEnvExtension_645_; lean_object* v_env_646_; lean_object* v_nextMacroScope_647_; lean_object* v_ngen_648_; lean_object* v_auxDeclNGen_649_; lean_object* v_traceState_650_; lean_object* v_messages_651_; lean_object* v_infoState_652_; lean_object* v_snapshotTasks_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_681_; 
v___x_644_ = lean_st_ref_take(v___y_643_);
v_toEnvExtension_645_ = lean_ctor_get(v___x_638_, 0);
v_env_646_ = lean_ctor_get(v___x_644_, 0);
v_nextMacroScope_647_ = lean_ctor_get(v___x_644_, 1);
v_ngen_648_ = lean_ctor_get(v___x_644_, 2);
v_auxDeclNGen_649_ = lean_ctor_get(v___x_644_, 3);
v_traceState_650_ = lean_ctor_get(v___x_644_, 4);
v_messages_651_ = lean_ctor_get(v___x_644_, 6);
v_infoState_652_ = lean_ctor_get(v___x_644_, 7);
v_snapshotTasks_653_ = lean_ctor_get(v___x_644_, 8);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_644_, 5);
lean_dec(v_unused_682_);
v___x_655_ = v___x_644_;
v_isShared_656_ = v_isSharedCheck_681_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snapshotTasks_653_);
lean_inc(v_infoState_652_);
lean_inc(v_messages_651_);
lean_inc(v_traceState_650_);
lean_inc(v_auxDeclNGen_649_);
lean_inc(v_ngen_648_);
lean_inc(v_nextMacroScope_647_);
lean_inc(v_env_646_);
lean_dec(v___x_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_681_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_asyncMode_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_asyncMode_657_ = lean_ctor_get(v_toEnvExtension_645_, 2);
v___x_658_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_638_, v_env_646_, v_entry_637_, v_asyncMode_657_, v___x_640_);
v___x_659_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__5);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 5, v___x_659_);
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_nextMacroScope_647_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_ngen_648_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_auxDeclNGen_649_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_traceState_650_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_messages_651_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_infoState_652_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_snapshotTasks_653_);
v___x_661_ = v_reuseFailAlloc_680_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_mctx_664_; lean_object* v_zetaDeltaFVarIds_665_; lean_object* v_postponed_666_; lean_object* v_diag_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
v___x_662_ = lean_st_ref_set(v___y_643_, v___x_661_);
v___x_663_ = lean_st_ref_take(v___y_642_);
v_mctx_664_ = lean_ctor_get(v___x_663_, 0);
v_zetaDeltaFVarIds_665_ = lean_ctor_get(v___x_663_, 2);
v_postponed_666_ = lean_ctor_get(v___x_663_, 3);
v_diag_667_ = lean_ctor_get(v___x_663_, 4);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_663_, 1);
lean_dec(v_unused_679_);
v___x_669_ = v___x_663_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_diag_667_);
lean_inc(v_postponed_666_);
lean_inc(v_zetaDeltaFVarIds_665_);
lean_inc(v_mctx_664_);
lean_dec(v___x_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__6);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_mctx_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_zetaDeltaFVarIds_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_postponed_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_diag_667_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_set(v___y_642_, v___x_673_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___boxed(lean_object* v_mod_723_, lean_object* v_isMeta_724_, lean_object* v_hint_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_isMeta_boxed_733_; lean_object* v_res_734_; 
v_isMeta_boxed_733_ = lean_unbox(v_isMeta_724_);
v_res_734_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0(v_mod_723_, v_isMeta_boxed_733_, v_hint_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1(lean_object* v___x_735_, lean_object* v_declName_736_, lean_object* v_as_737_, size_t v_sz_738_, size_t v_i_739_, lean_object* v_b_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_739_, v_sz_738_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v_declName_736_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_b_740_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; lean_object* v_modules_751_; lean_object* v___x_752_; lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v_toImport_755_; lean_object* v_module_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v___x_750_ = l_Lean_Environment_header(v___x_735_);
v_modules_751_ = lean_ctor_get(v___x_750_, 3);
lean_inc_ref(v_modules_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_753_ = lean_array_uget_borrowed(v_as_737_, v_i_739_);
v___x_754_ = lean_array_get(v___x_752_, v_modules_751_, v_a_753_);
lean_dec_ref(v_modules_751_);
v_toImport_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_toImport_755_);
lean_dec(v___x_754_);
v_module_756_ = lean_ctor_get(v_toImport_755_, 0);
lean_inc(v_module_756_);
lean_dec_ref(v_toImport_755_);
v___x_757_ = 0;
lean_inc(v_declName_736_);
v___x_758_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0(v_module_756_, v___x_757_, v_declName_736_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; size_t v___x_760_; size_t v___x_761_; 
lean_dec_ref(v___x_758_);
v___x_759_ = lean_box(0);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_add(v_i_739_, v___x_760_);
v_i_739_ = v___x_761_;
v_b_740_ = v___x_759_;
goto _start;
}
else
{
lean_dec(v_declName_736_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1___boxed(lean_object* v___x_763_, lean_object* v_declName_764_, lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
size_t v_sz_boxed_776_; size_t v_i_boxed_777_; lean_object* v_res_778_; 
v_sz_boxed_776_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_777_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1(v___x_763_, v_declName_764_, v_as_765_, v_sz_boxed_776_, v_i_boxed_777_, v_b_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec_ref(v_as_765_);
lean_dec_ref(v___x_763_);
return v_res_778_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__1));
v___x_782_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__0));
v___x_783_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_782_, v___x_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0(lean_object* v_declName_786_, uint8_t v_isMeta_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_env_799_; lean_object* v___y_801_; lean_object* v___x_814_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
v_env_799_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_env_799_);
lean_dec(v___x_795_);
v___x_814_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_799_, v_declName_786_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref(v_env_799_);
lean_dec(v_declName_786_);
goto v___jp_796_;
}
else
{
lean_object* v_val_815_; lean_object* v___x_816_; lean_object* v_modules_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_val_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Lean_Environment_header(v_env_799_);
v_modules_817_ = lean_ctor_get(v___x_816_, 3);
lean_inc_ref(v_modules_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = lean_array_get_size(v_modules_817_);
v___x_819_ = lean_nat_dec_lt(v_val_815_, v___x_818_);
if (v___x_819_ == 0)
{
lean_dec_ref(v_modules_817_);
lean_dec(v_val_815_);
lean_dec_ref(v_env_799_);
lean_dec(v_declName_786_);
goto v___jp_796_;
}
else
{
lean_object* v___x_820_; lean_object* v_env_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___y_825_; 
v___x_820_ = lean_st_ref_get(v___y_793_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_env_821_);
lean_dec(v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__2);
v___x_823_ = lean_array_fget(v_modules_817_, v_val_815_);
lean_dec(v_val_815_);
lean_dec_ref(v_modules_817_);
if (v_isMeta_787_ == 0)
{
lean_dec_ref(v_env_821_);
v___y_825_ = v_isMeta_787_;
goto v___jp_824_;
}
else
{
uint8_t v___x_836_; 
lean_inc(v_declName_786_);
v___x_836_ = l_Lean_isMarkedMeta(v_env_821_, v_declName_786_);
if (v___x_836_ == 0)
{
v___y_825_ = v_isMeta_787_;
goto v___jp_824_;
}
else
{
uint8_t v___x_837_; 
v___x_837_ = 0;
v___y_825_ = v___x_837_;
goto v___jp_824_;
}
}
v___jp_824_:
{
lean_object* v_toImport_826_; lean_object* v_module_827_; lean_object* v___x_828_; 
v_toImport_826_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_toImport_826_);
lean_dec(v___x_823_);
v_module_827_ = lean_ctor_get(v_toImport_826_, 0);
lean_inc(v_module_827_);
lean_dec_ref(v_toImport_826_);
lean_inc(v_declName_786_);
v___x_828_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0(v_module_827_, v___y_825_, v_declName_786_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_828_);
v___x_829_ = l_Lean_indirectModUseExt;
v___x_830_ = lean_box(1);
v___x_831_ = lean_box(0);
lean_inc_ref(v_env_799_);
v___x_832_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_822_, v___x_829_, v_env_799_, v___x_830_, v___x_831_);
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg(v___x_832_, v_declName_786_);
lean_dec(v___x_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_834_; 
v___x_834_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___closed__3));
v___y_801_ = v___x_834_;
goto v___jp_800_;
}
else
{
lean_object* v_val_835_; 
v_val_835_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_835_);
lean_dec_ref(v___x_833_);
v___y_801_ = v_val_835_;
goto v___jp_800_;
}
}
else
{
lean_dec_ref(v_env_799_);
lean_dec(v_declName_786_);
return v___x_828_;
}
}
}
}
v___jp_796_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
v___jp_800_:
{
lean_object* v___x_802_; size_t v_sz_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_802_ = lean_box(0);
v_sz_803_ = lean_array_size(v___y_801_);
v___x_804_ = ((size_t)0ULL);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__1(v_env_799_, v_declName_786_, v___y_801_, v_sz_803_, v___x_804_, v___x_802_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_env_799_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_805_, 0);
lean_dec(v_unused_813_);
v___x_807_ = v___x_805_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_dec(v___x_805_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_802_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_802_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0___boxed(lean_object* v_declName_838_, lean_object* v_isMeta_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v_isMeta_boxed_847_; lean_object* v_res_848_; 
v_isMeta_boxed_847_ = lean_unbox(v_isMeta_839_);
v_res_848_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0(v_declName_838_, v_isMeta_boxed_847_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_848_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0));
v___x_851_ = l_Lean_stringToMessageData(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__2));
v___x_854_ = l_Lean_stringToMessageData(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__4));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__6));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_));
v___x_862_ = l_Lean_MessageData_ofName(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__8);
v___x_864_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__7);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object* v_optConfig_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; uint8_t v_recover_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; 
v_recover_911_ = lean_ctor_get_uint8(v_a_871_, sizeof(void*)*1);
lean_inc(v_optConfig_870_);
v___x_912_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_870_);
v___x_913_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_912_);
v___x_914_ = lean_array_get_size(v___x_913_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_nat_dec_eq(v___x_914_, v___x_915_);
v___x_917_ = 1;
if (v___x_916_ == 0)
{
lean_object* v___x_966_; lean_object* v_fileName_967_; lean_object* v_fileMap_968_; lean_object* v_options_969_; lean_object* v_currRecDepth_970_; lean_object* v_maxRecDepth_971_; lean_object* v_ref_972_; lean_object* v_currNamespace_973_; lean_object* v_openDecls_974_; lean_object* v_initHeartbeats_975_; lean_object* v_maxHeartbeats_976_; lean_object* v_quotContext_977_; lean_object* v_currMacroScope_978_; uint8_t v_diag_979_; lean_object* v_cancelTk_x3f_980_; uint8_t v_suppressElabErrors_981_; lean_object* v_inheritedTraceOptions_982_; lean_object* v_env_983_; lean_object* v_ref_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_966_ = lean_st_ref_get(v_a_877_);
v_fileName_967_ = lean_ctor_get(v_a_876_, 0);
v_fileMap_968_ = lean_ctor_get(v_a_876_, 1);
v_options_969_ = lean_ctor_get(v_a_876_, 2);
v_currRecDepth_970_ = lean_ctor_get(v_a_876_, 3);
v_maxRecDepth_971_ = lean_ctor_get(v_a_876_, 4);
v_ref_972_ = lean_ctor_get(v_a_876_, 5);
v_currNamespace_973_ = lean_ctor_get(v_a_876_, 6);
v_openDecls_974_ = lean_ctor_get(v_a_876_, 7);
v_initHeartbeats_975_ = lean_ctor_get(v_a_876_, 8);
v_maxHeartbeats_976_ = lean_ctor_get(v_a_876_, 9);
v_quotContext_977_ = lean_ctor_get(v_a_876_, 10);
v_currMacroScope_978_ = lean_ctor_get(v_a_876_, 11);
v_diag_979_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*14);
v_cancelTk_x3f_980_ = lean_ctor_get(v_a_876_, 12);
v_suppressElabErrors_981_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_982_ = lean_ctor_get(v_a_876_, 13);
v_env_983_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_966_);
v_ref_984_ = l_Lean_replaceRef(v_optConfig_870_, v_ref_972_);
lean_dec(v_optConfig_870_);
lean_inc_ref(v_inheritedTraceOptions_982_);
lean_inc(v_cancelTk_x3f_980_);
lean_inc(v_currMacroScope_978_);
lean_inc(v_quotContext_977_);
lean_inc(v_maxHeartbeats_976_);
lean_inc(v_initHeartbeats_975_);
lean_inc(v_openDecls_974_);
lean_inc(v_currNamespace_973_);
lean_inc(v_maxRecDepth_971_);
lean_inc(v_currRecDepth_970_);
lean_inc_ref(v_options_969_);
lean_inc_ref(v_fileMap_968_);
lean_inc_ref(v_fileName_967_);
v___x_985_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_985_, 0, v_fileName_967_);
lean_ctor_set(v___x_985_, 1, v_fileMap_968_);
lean_ctor_set(v___x_985_, 2, v_options_969_);
lean_ctor_set(v___x_985_, 3, v_currRecDepth_970_);
lean_ctor_set(v___x_985_, 4, v_maxRecDepth_971_);
lean_ctor_set(v___x_985_, 5, v_ref_984_);
lean_ctor_set(v___x_985_, 6, v_currNamespace_973_);
lean_ctor_set(v___x_985_, 7, v_openDecls_974_);
lean_ctor_set(v___x_985_, 8, v_initHeartbeats_975_);
lean_ctor_set(v___x_985_, 9, v_maxHeartbeats_976_);
lean_ctor_set(v___x_985_, 10, v_quotContext_977_);
lean_ctor_set(v___x_985_, 11, v_currMacroScope_978_);
lean_ctor_set(v___x_985_, 12, v_cancelTk_x3f_980_);
lean_ctor_set(v___x_985_, 13, v_inheritedTraceOptions_982_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*14, v_diag_979_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*14 + 1, v_suppressElabErrors_981_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_));
v___x_987_ = l_Lean_Environment_contains(v_env_983_, v___x_986_, v___x_917_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v___x_913_);
v___x_988_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__9);
v___x_989_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(v___x_988_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v___x_985_, v_a_877_);
lean_dec_ref(v___x_985_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
v___y_919_ = v_a_872_;
v___y_920_ = v_a_873_;
v___y_921_ = v_a_874_;
v___y_922_ = v_a_875_;
v___y_923_ = v___x_985_;
v___y_924_ = v_a_877_;
goto v___jp_918_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v___x_913_);
lean_dec(v_optConfig_870_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__10));
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
v___jp_879_:
{
if (v___y_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v___y_887_);
v___x_890_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__1);
v___x_891_ = l_Lean_MessageData_ofExpr(v___y_884_);
v___x_892_ = l_Lean_indentD(v___x_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_890_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__3);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_Exception_toMessageData(v___y_888_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(v___x_897_, v___y_886_, v___y_883_, v___y_880_, v___y_882_, v___y_885_, v___y_881_);
lean_dec_ref(v___y_885_);
return v___x_898_;
}
else
{
lean_dec_ref(v___y_888_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
return v___y_887_;
}
}
v___jp_899_:
{
lean_object* v___x_907_; 
lean_inc_ref(v___y_900_);
v___x_907_ = l_Lean_Elab_Tactic_Do_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_(v___y_900_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_dec_ref(v___y_905_);
lean_dec_ref(v___y_900_);
return v___x_907_;
}
else
{
lean_object* v_a_908_; uint8_t v___x_909_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
v___x_909_ = l_Lean_Exception_isInterrupt(v_a_908_);
if (v___x_909_ == 0)
{
uint8_t v___x_910_; 
lean_inc(v_a_908_);
v___x_910_ = l_Lean_Exception_isRuntime(v_a_908_);
v___y_880_ = v___y_903_;
v___y_881_ = v___y_906_;
v___y_882_ = v___y_904_;
v___y_883_ = v___y_902_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_905_;
v___y_886_ = v___y_901_;
v___y_887_ = v___x_907_;
v___y_888_ = v_a_908_;
v___y_889_ = v___x_910_;
goto v___jp_879_;
}
else
{
v___y_880_ = v___y_903_;
v___y_881_ = v___y_906_;
v___y_882_ = v___y_904_;
v___y_883_ = v___y_902_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_905_;
v___y_886_ = v___y_901_;
v___y_887_ = v___x_907_;
v___y_888_ = v_a_908_;
v___y_889_ = v___x_909_;
goto v___jp_879_;
}
}
}
v___jp_918_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_3659318125____hygCtx___hyg_3_));
v___x_926_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0(v___x_925_, v___x_917_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_927_; 
lean_dec_ref(v___x_926_);
v___x_927_ = l_Lean_Elab_Tactic_elabConfig(v_recover_911_, v___x_925_, v___x_913_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_949_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_949_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_949_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_949_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_Expr_hasSyntheticSorry(v_a_928_);
if (v___x_932_ == 0)
{
uint8_t v___x_933_; 
lean_del_object(v___x_930_);
v___x_933_ = l_Lean_Expr_hasSorry(v_a_928_);
if (v___x_933_ == 0)
{
v___y_900_ = v_a_928_;
v___y_901_ = v___y_919_;
v___y_902_ = v___y_920_;
v___y_903_ = v___y_921_;
v___y_904_ = v___y_922_;
v___y_905_ = v___y_923_;
v___y_906_ = v___y_924_;
goto v___jp_899_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_a_928_);
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__5);
v___x_935_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(v___x_934_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec_ref(v___y_923_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec(v_a_928_);
lean_dec_ref(v___y_923_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_917_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1 + 1, v___x_917_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1 + 2, v___x_917_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1 + 3, v___x_916_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_945_);
v___x_947_ = v___x_930_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
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
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___y_923_);
v_a_950_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_927_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_927_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___y_923_);
lean_dec_ref(v___x_913_);
v_a_958_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_926_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_926_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object* v_optConfig_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_a_1001_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object* v_optConfig_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_1010_, v_a_1011_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object* v_optConfig_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Elab_Tactic_Do_elabConfig(v_optConfig_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1(lean_object* v_00_u03b1_1032_, lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___redArg(v_msg_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1(v_00_u03b1_1042_, v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2(lean_object* v_00_u03b2_1052_, lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___redArg(v_m_1053_, v_a_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1056_, lean_object* v_m_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2(v_00_u03b2_1056_, v_m_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_m_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5(lean_object* v_msgData_1060_, lean_object* v_macroStack_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___redArg(v_msgData_1060_, v_macroStack_1061_, v___y_1066_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5___boxed(lean_object* v_msgData_1070_, lean_object* v_macroStack_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__5(v_msgData_1070_, v_macroStack_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1079_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___redArg(v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1(v_00_u03b2_1084_, v_x_1085_, v_x_1086_);
lean_dec_ref(v_x_1086_);
lean_dec_ref(v_x_1085_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2(lean_object* v_cls_1089_, lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___redArg(v_cls_1089_, v_msg_1090_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1099_, lean_object* v_msg_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__2(v_cls_1099_, v_msg_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1109_, lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___redArg(v_a_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_a_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__2_spec__5(v_00_u03b2_1113_, v_a_1114_, v_x_1115_);
lean_dec(v_x_1115_);
lean_dec(v_a_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, size_t v_x_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1118_, v_x_1119_, v_x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
size_t v_x_13572__boxed_1126_; uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_x_13572__boxed_1126_ = lean_unbox_usize(v_x_1124_);
lean_dec(v_x_1124_);
v_res_1127_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1122_, v_x_1123_, v_x_13572__boxed_1126_, v_x_1125_);
lean_dec_ref(v_x_1125_);
lean_dec_ref(v_x_1123_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1129_, lean_object* v_keys_1130_, lean_object* v_vals_1131_, lean_object* v_heq_1132_, lean_object* v_i_1133_, lean_object* v_k_1134_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_keys_1130_, v_i_1133_, v_k_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_k_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4_spec__9(v_00_u03b2_1136_, v_keys_1137_, v_vals_1138_, v_heq_1139_, v_i_1140_, v_k_1141_);
lean_dec_ref(v_k_1141_);
lean_dec_ref(v_vals_1138_);
lean_dec_ref(v_keys_1137_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1149_; lean_object* v_fuel_1150_; 
v___x_1149_ = lean_st_ref_get(v_a_1144_);
v_fuel_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fuel_1150_);
if (lean_obj_tag(v_fuel_1150_) == 0)
{
lean_object* v_simpState_1151_; lean_object* v_invariants_1152_; lean_object* v_vcs_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1174_; 
v_simpState_1151_ = lean_ctor_get(v___x_1149_, 1);
v_invariants_1152_ = lean_ctor_get(v___x_1149_, 2);
v_vcs_1153_ = lean_ctor_get(v___x_1149_, 3);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1175_);
v___x_1155_ = v___x_1149_;
v_isShared_1156_ = v_isSharedCheck_1174_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_vcs_1153_);
lean_inc(v_invariants_1152_);
lean_inc(v_simpState_1151_);
lean_dec(v___x_1149_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1174_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_n_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1173_; 
v_n_1157_ = lean_ctor_get(v_fuel_1150_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_fuel_1150_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1159_ = v_fuel_1150_;
v_isShared_1160_ = v_isSharedCheck_1173_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_n_1157_);
lean_dec(v_fuel_1150_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1173_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_zero_1161_; uint8_t v_isZero_1162_; 
v_zero_1161_ = lean_unsigned_to_nat(0u);
v_isZero_1162_ = lean_nat_dec_eq(v_n_1157_, v_zero_1161_);
if (v_isZero_1162_ == 1)
{
lean_del_object(v___x_1159_);
lean_dec(v_n_1157_);
lean_del_object(v___x_1155_);
lean_dec_ref(v_vcs_1153_);
lean_dec_ref(v_invariants_1152_);
lean_dec_ref(v_simpState_1151_);
goto v___jp_1146_;
}
else
{
lean_object* v_one_1163_; lean_object* v_n_1164_; lean_object* v___x_1166_; 
v_one_1163_ = lean_unsigned_to_nat(1u);
v_n_1164_ = lean_nat_sub(v_n_1157_, v_one_1163_);
lean_dec(v_n_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_n_1164_);
v___x_1166_ = v___x_1159_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_n_1164_);
v___x_1166_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1166_);
v___x_1168_ = v___x_1155_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_simpState_1151_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_invariants_1152_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_vcs_1153_);
v___x_1168_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_st_ref_set(v_a_1144_, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1149_);
goto v___jp_1146_;
}
v___jp_1146_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1176_);
lean_dec(v_a_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1180_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_Tactic_Do_burnOne(v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object* v_x_1195_, lean_object* v_k_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v_fuel_1205_; 
v___x_1204_ = lean_st_ref_get(v_a_1198_);
v_fuel_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_fuel_1205_);
lean_dec(v___x_1204_);
if (lean_obj_tag(v_fuel_1205_) == 0)
{
lean_object* v_n_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_n_1206_ = lean_ctor_get(v_fuel_1205_, 0);
lean_inc(v_n_1206_);
lean_dec_ref(v_fuel_1205_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_nat_dec_eq(v_n_1206_, v___x_1207_);
lean_dec(v_n_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v_x_1195_);
lean_inc(v_a_1202_);
lean_inc_ref(v_a_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
lean_inc(v_a_1198_);
lean_inc_ref(v_a_1197_);
v___x_1209_ = lean_apply_7(v_k_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, lean_box(0));
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; 
lean_dec_ref(v_k_1196_);
lean_inc(v_a_1202_);
lean_inc_ref(v_a_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
lean_inc(v_a_1198_);
lean_inc_ref(v_a_1197_);
v___x_1210_ = lean_apply_7(v_x_1195_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, lean_box(0));
return v___x_1210_;
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v_fuel_1205_);
lean_dec_ref(v_x_1195_);
lean_inc(v_a_1202_);
lean_inc_ref(v_a_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
lean_inc(v_a_1198_);
lean_inc_ref(v_a_1197_);
v___x_1211_ = lean_apply_7(v_k_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, lean_box(0));
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object* v_x_1212_, lean_object* v_k_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1212_, v_k_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object* v_00_u03b1_1222_, lean_object* v_x_1223_, lean_object* v_k_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1223_, v_k_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_x_1234_, lean_object* v_k_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel(v_00_u03b1_1233_, v_x_1234_, v_k_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_ref_1250_; lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1260_; 
v_ref_1250_ = lean_ctor_get(v___y_1247_, 5);
v___x_1251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(v_msg_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_inc(v_ref_1250_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_ref_1250_);
lean_ctor_set(v___x_1256_, 1, v_a_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 1);
lean_ctor_set(v___x_1254_, 0, v___x_1256_);
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(v_msg_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v_ks_1272_; lean_object* v_vs_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1297_; 
v_ks_1272_ = lean_ctor_get(v_x_1268_, 0);
v_vs_1273_ = lean_ctor_get(v_x_1268_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1275_ = v_x_1268_;
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_vs_1273_);
lean_inc(v_ks_1272_);
lean_dec(v_x_1268_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_array_get_size(v_ks_1272_);
v___x_1278_ = lean_nat_dec_lt(v_x_1269_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec(v_x_1269_);
v___x_1279_ = lean_array_push(v_ks_1272_, v_x_1270_);
v___x_1280_ = lean_array_push(v_vs_1273_, v_x_1271_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1280_);
lean_ctor_set(v___x_1275_, 0, v___x_1279_);
v___x_1282_ = v___x_1275_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v_k_x27_1284_; uint8_t v___x_1285_; 
v_k_x27_1284_ = lean_array_fget_borrowed(v_ks_1272_, v_x_1269_);
v___x_1285_ = l_Lean_instBEqMVarId_beq(v_x_1270_, v_k_x27_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1287_; 
if (v_isShared_1276_ == 0)
{
v___x_1287_ = v___x_1275_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_ks_1272_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_vs_1273_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_x_1269_, v___x_1288_);
lean_dec(v_x_1269_);
v_x_1268_ = v___x_1287_;
v_x_1269_ = v___x_1289_;
goto _start;
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = lean_array_fset(v_ks_1272_, v_x_1269_, v_x_1270_);
v___x_1293_ = lean_array_fset(v_vs_1273_, v_x_1269_, v_x_1271_);
lean_dec(v_x_1269_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1293_);
lean_ctor_set(v___x_1275_, 0, v___x_1292_);
v___x_1295_ = v___x_1275_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1293_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_n_1298_, lean_object* v_k_1299_, lean_object* v_v_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_n_1298_, v___x_1301_, v_k_1299_, v_v_1300_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1304_, size_t v_x_1305_, size_t v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_es_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; lean_object* v_j_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_es_1309_ = lean_ctor_get(v_x_1304_, 0);
v___x_1310_ = ((size_t)5ULL);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1313_ = lean_usize_land(v_x_1305_, v___x_1312_);
v_j_1314_ = lean_usize_to_nat(v___x_1313_);
v___x_1315_ = lean_array_get_size(v_es_1309_);
v___x_1316_ = lean_nat_dec_lt(v_j_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec(v_j_1314_);
lean_dec(v_x_1308_);
lean_dec(v_x_1307_);
return v_x_1304_;
}
else
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1353_; 
lean_inc_ref(v_es_1309_);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v_x_1304_, 0);
lean_dec(v_unused_1354_);
v___x_1318_ = v_x_1304_;
v_isShared_1319_ = v_isSharedCheck_1353_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_x_1304_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1353_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_v_1320_; lean_object* v___x_1321_; lean_object* v_xs_x27_1322_; lean_object* v___y_1324_; 
v_v_1320_ = lean_array_fget(v_es_1309_, v_j_1314_);
v___x_1321_ = lean_box(0);
v_xs_x27_1322_ = lean_array_fset(v_es_1309_, v_j_1314_, v___x_1321_);
switch(lean_obj_tag(v_v_1320_))
{
case 0:
{
lean_object* v_key_1329_; lean_object* v_val_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1340_; 
v_key_1329_ = lean_ctor_get(v_v_1320_, 0);
v_val_1330_ = lean_ctor_get(v_v_1320_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_v_1320_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1332_ = v_v_1320_;
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_val_1330_);
lean_inc(v_key_1329_);
lean_dec(v_v_1320_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___x_1334_; 
v___x_1334_ = l_Lean_instBEqMVarId_beq(v_x_1307_, v_key_1329_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_del_object(v___x_1332_);
v___x_1335_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1329_, v_val_1330_, v_x_1307_, v_x_1308_);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
v___y_1324_ = v___x_1336_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_val_1330_);
lean_dec(v_key_1329_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v_x_1308_);
lean_ctor_set(v___x_1332_, 0, v_x_1307_);
v___x_1338_ = v___x_1332_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_x_1307_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_x_1308_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v___y_1324_ = v___x_1338_;
goto v___jp_1323_;
}
}
}
}
case 1:
{
lean_object* v_node_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1351_; 
v_node_1341_ = lean_ctor_get(v_v_1320_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_v_1320_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1343_ = v_v_1320_;
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_node_1341_);
lean_dec(v_v_1320_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1345_ = lean_usize_shift_right(v_x_1305_, v___x_1310_);
v___x_1346_ = lean_usize_add(v_x_1306_, v___x_1311_);
v___x_1347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_node_1341_, v___x_1345_, v___x_1346_, v_x_1307_, v_x_1308_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1347_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
v___y_1324_ = v___x_1349_;
goto v___jp_1323_;
}
}
}
default: 
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_x_1307_);
lean_ctor_set(v___x_1352_, 1, v_x_1308_);
v___y_1324_ = v___x_1352_;
goto v___jp_1323_;
}
}
v___jp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = lean_array_fset(v_xs_x27_1322_, v_j_1314_, v___y_1324_);
lean_dec(v_j_1314_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1325_);
v___x_1327_ = v___x_1318_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
else
{
lean_object* v_ks_1355_; lean_object* v_vs_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1376_; 
v_ks_1355_ = lean_ctor_get(v_x_1304_, 0);
v_vs_1356_ = lean_ctor_get(v_x_1304_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1358_ = v_x_1304_;
v_isShared_1359_ = v_isSharedCheck_1376_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_vs_1356_);
lean_inc(v_ks_1355_);
lean_dec(v_x_1304_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1376_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_ks_1355_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_vs_1356_);
v___x_1361_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v_newNode_1362_; uint8_t v___y_1364_; size_t v___x_1370_; uint8_t v___x_1371_; 
v_newNode_1362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v___x_1361_, v_x_1307_, v_x_1308_);
v___x_1370_ = ((size_t)7ULL);
v___x_1371_ = lean_usize_dec_le(v___x_1370_, v_x_1306_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1362_);
v___x_1373_ = lean_unsigned_to_nat(4u);
v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1373_);
lean_dec(v___x_1372_);
v___y_1364_ = v___x_1374_;
goto v___jp_1363_;
}
else
{
v___y_1364_ = v___x_1371_;
goto v___jp_1363_;
}
v___jp_1363_:
{
if (v___y_1364_ == 0)
{
lean_object* v_ks_1365_; lean_object* v_vs_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_ks_1365_ = lean_ctor_get(v_newNode_1362_, 0);
lean_inc_ref(v_ks_1365_);
v_vs_1366_ = lean_ctor_get(v_newNode_1362_, 1);
lean_inc_ref(v_vs_1366_);
lean_dec_ref(v_newNode_1362_);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1306_, v_ks_1365_, v_vs_1366_, v___x_1367_, v___x_1368_);
lean_dec_ref(v_vs_1366_);
lean_dec_ref(v_ks_1365_);
return v___x_1369_;
}
else
{
return v_newNode_1362_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(size_t v_depth_1377_, lean_object* v_keys_1378_, lean_object* v_vals_1379_, lean_object* v_i_1380_, lean_object* v_entries_1381_){
_start:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_array_get_size(v_keys_1378_);
v___x_1383_ = lean_nat_dec_lt(v_i_1380_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec(v_i_1380_);
return v_entries_1381_;
}
else
{
lean_object* v_k_1384_; lean_object* v_v_1385_; uint64_t v___x_1386_; size_t v_h_1387_; size_t v___x_1388_; lean_object* v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; size_t v_h_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_k_1384_ = lean_array_fget_borrowed(v_keys_1378_, v_i_1380_);
v_v_1385_ = lean_array_fget_borrowed(v_vals_1379_, v_i_1380_);
v___x_1386_ = l_Lean_instHashableMVarId_hash(v_k_1384_);
v_h_1387_ = lean_uint64_to_usize(v___x_1386_);
v___x_1388_ = ((size_t)5ULL);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_sub(v_depth_1377_, v___x_1390_);
v___x_1392_ = lean_usize_mul(v___x_1388_, v___x_1391_);
v_h_1393_ = lean_usize_shift_right(v_h_1387_, v___x_1392_);
v___x_1394_ = lean_nat_add(v_i_1380_, v___x_1389_);
lean_dec(v_i_1380_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
v___x_1395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_entries_1381_, v_h_1393_, v_depth_1377_, v_k_1384_, v_v_1385_);
v_i_1380_ = v___x_1394_;
v_entries_1381_ = v___x_1395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1397_, lean_object* v_keys_1398_, lean_object* v_vals_1399_, lean_object* v_i_1400_, lean_object* v_entries_1401_){
_start:
{
size_t v_depth_boxed_1402_; lean_object* v_res_1403_; 
v_depth_boxed_1402_ = lean_unbox_usize(v_depth_1397_);
lean_dec(v_depth_1397_);
v_res_1403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1402_, v_keys_1398_, v_vals_1399_, v_i_1400_, v_entries_1401_);
lean_dec_ref(v_vals_1399_);
lean_dec_ref(v_keys_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
size_t v_x_8076__boxed_1409_; size_t v_x_8077__boxed_1410_; lean_object* v_res_1411_; 
v_x_8076__boxed_1409_ = lean_unbox_usize(v_x_1405_);
lean_dec(v_x_1405_);
v_x_8077__boxed_1410_ = lean_unbox_usize(v_x_1406_);
lean_dec(v_x_1406_);
v_res_1411_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1404_, v_x_8076__boxed_1409_, v_x_8077__boxed_1410_, v_x_1407_, v_x_1408_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
uint64_t v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = l_Lean_instHashableMVarId_hash(v_x_1413_);
v___x_1416_ = lean_uint64_to_usize(v___x_1415_);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1412_, v___x_1416_, v___x_1417_, v_x_1413_, v_x_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(lean_object* v_range_1419_, lean_object* v_b_1420_, lean_object* v_i_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_stop_1425_; lean_object* v_step_1426_; lean_object* v_a_1428_; lean_object* v___y_1432_; uint8_t v___x_1448_; 
v_stop_1425_ = lean_ctor_get(v_range_1419_, 1);
v_step_1426_ = lean_ctor_get(v_range_1419_, 2);
v___x_1448_ = lean_nat_dec_lt(v_i_1421_, v_stop_1425_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_i_1421_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_b_1420_);
return v___x_1449_;
}
else
{
lean_object* v_decls_1450_; lean_object* v_size_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_decls_1450_ = lean_ctor_get(v_b_1420_, 1);
v_size_1451_ = lean_ctor_get(v_decls_1450_, 2);
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_nat_dec_lt(v_i_1421_, v_size_1451_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = l_outOfBounds___redArg(v___x_1452_);
v___y_1432_ = v___x_1454_;
goto v___jp_1431_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1452_, v_decls_1450_, v_i_1421_);
v___y_1432_ = v___x_1455_;
goto v___jp_1431_;
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_nat_add(v_i_1421_, v_step_1426_);
lean_dec(v_i_1421_);
v_b_1420_ = v_a_1428_;
v_i_1421_ = v___x_1429_;
goto _start;
}
v___jp_1431_:
{
if (lean_obj_tag(v___y_1432_) == 1)
{
lean_object* v_val_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_val_1433_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref(v___y_1432_);
v___x_1434_ = l_Lean_LocalDecl_userName(v_val_1433_);
v___x_1435_ = l_Lean_Name_hasMacroScopes(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Core_mkFreshUserName(v___x_1434_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = l_Lean_LocalDecl_fvarId(v_val_1433_);
lean_dec(v_val_1433_);
v___x_1439_ = l_Lean_LocalContext_setUserName(v_b_1420_, v___x_1438_, v_a_1437_);
v_a_1428_ = v___x_1439_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_val_1433_);
lean_dec(v_i_1421_);
lean_dec_ref(v_b_1420_);
v_a_1440_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1436_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1436_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_dec(v___x_1434_);
lean_dec(v_val_1433_);
v_a_1428_ = v_b_1420_;
goto v___jp_1427_;
}
}
else
{
lean_dec(v___y_1432_);
v_a_1428_ = v_b_1420_;
goto v___jp_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_range_1456_, lean_object* v_b_1457_, lean_object* v_i_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_1456_, v_b_1457_, v_i_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_range_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(lean_object* v_lctx_1463_, lean_object* v_idx_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v_lctx_1463_);
v___x_1472_ = lean_local_ctx_num_indices(v_lctx_1463_);
v___x_1473_ = lean_unsigned_to_nat(1u);
lean_inc(v_idx_1464_);
v___x_1474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1474_, 0, v_idx_1464_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set(v___x_1474_, 2, v___x_1473_);
v___x_1475_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v___x_1474_, v_lctx_1463_, v_idx_1464_, v___y_1469_, v___y_1470_);
lean_dec_ref(v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0___boxed(lean_object* v_lctx_1476_, lean_object* v_idx_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_1476_, v_idx_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1485_;
}
}
static lean_object* _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(lean_object* v_mvarId_1489_, lean_object* v_idx_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v_mctx_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_st_ref_get(v___y_1494_);
v_mctx_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_mctx_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1499_, v_mvarId_1489_);
if (lean_obj_tag(v___x_1500_) == 1)
{
lean_object* v_val_1501_; lean_object* v_userName_1502_; lean_object* v_lctx_1503_; lean_object* v_type_1504_; lean_object* v_depth_1505_; lean_object* v_localInstances_1506_; uint8_t v_kind_1507_; lean_object* v_numScopeArgs_1508_; lean_object* v_index_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1565_; 
v_val_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_val_1501_);
lean_dec_ref(v___x_1500_);
v_userName_1502_ = lean_ctor_get(v_val_1501_, 0);
v_lctx_1503_ = lean_ctor_get(v_val_1501_, 1);
v_type_1504_ = lean_ctor_get(v_val_1501_, 2);
v_depth_1505_ = lean_ctor_get(v_val_1501_, 3);
v_localInstances_1506_ = lean_ctor_get(v_val_1501_, 4);
v_kind_1507_ = lean_ctor_get_uint8(v_val_1501_, sizeof(void*)*7);
v_numScopeArgs_1508_ = lean_ctor_get(v_val_1501_, 5);
v_index_1509_ = lean_ctor_get(v_val_1501_, 6);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_val_1501_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1511_ = v_val_1501_;
v_isShared_1512_ = v_isSharedCheck_1565_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_index_1509_);
lean_inc(v_numScopeArgs_1508_);
lean_inc(v_localInstances_1506_);
lean_inc(v_depth_1505_);
lean_inc(v_type_1504_);
lean_inc(v_lctx_1503_);
lean_inc(v_userName_1502_);
lean_dec(v_val_1501_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1565_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_1503_, v_idx_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1556_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1556_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1556_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v_mctx_1519_; lean_object* v_cache_1520_; lean_object* v_zetaDeltaFVarIds_1521_; lean_object* v_postponed_1522_; lean_object* v_diag_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1555_; 
v___x_1518_ = lean_st_ref_take(v___y_1494_);
v_mctx_1519_ = lean_ctor_get(v___x_1518_, 0);
v_cache_1520_ = lean_ctor_get(v___x_1518_, 1);
v_zetaDeltaFVarIds_1521_ = lean_ctor_get(v___x_1518_, 2);
v_postponed_1522_ = lean_ctor_get(v___x_1518_, 3);
v_diag_1523_ = lean_ctor_get(v___x_1518_, 4);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1525_ = v___x_1518_;
v_isShared_1526_ = v_isSharedCheck_1555_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_diag_1523_);
lean_inc(v_postponed_1522_);
lean_inc(v_zetaDeltaFVarIds_1521_);
lean_inc(v_cache_1520_);
lean_inc(v_mctx_1519_);
lean_dec(v___x_1518_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1555_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_depth_1527_; lean_object* v_levelAssignDepth_1528_; lean_object* v_mvarCounter_1529_; lean_object* v_lDepth_1530_; lean_object* v_decls_1531_; lean_object* v_userNames_1532_; lean_object* v_lAssignment_1533_; lean_object* v_eAssignment_1534_; lean_object* v_dAssignment_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1554_; 
v_depth_1527_ = lean_ctor_get(v_mctx_1519_, 0);
v_levelAssignDepth_1528_ = lean_ctor_get(v_mctx_1519_, 1);
v_mvarCounter_1529_ = lean_ctor_get(v_mctx_1519_, 2);
v_lDepth_1530_ = lean_ctor_get(v_mctx_1519_, 3);
v_decls_1531_ = lean_ctor_get(v_mctx_1519_, 4);
v_userNames_1532_ = lean_ctor_get(v_mctx_1519_, 5);
v_lAssignment_1533_ = lean_ctor_get(v_mctx_1519_, 6);
v_eAssignment_1534_ = lean_ctor_get(v_mctx_1519_, 7);
v_dAssignment_1535_ = lean_ctor_get(v_mctx_1519_, 8);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_mctx_1519_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1537_ = v_mctx_1519_;
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_dAssignment_1535_);
lean_inc(v_eAssignment_1534_);
lean_inc(v_lAssignment_1533_);
lean_inc(v_userNames_1532_);
lean_inc(v_decls_1531_);
lean_inc(v_lDepth_1530_);
lean_inc(v_mvarCounter_1529_);
lean_inc(v_levelAssignDepth_1528_);
lean_inc(v_depth_1527_);
lean_dec(v_mctx_1519_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v_a_1514_);
v___x_1540_ = v___x_1511_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_userName_1502_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_a_1514_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_type_1504_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_depth_1505_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_localInstances_1506_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_numScopeArgs_1508_);
lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_index_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1553_, sizeof(void*)*7, v_kind_1507_);
v___x_1540_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_decls_1531_, v_mvarId_1489_, v___x_1540_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v___x_1541_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_depth_1527_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_levelAssignDepth_1528_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_mvarCounter_1529_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_lDepth_1530_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 5, v_userNames_1532_);
lean_ctor_set(v_reuseFailAlloc_1552_, 6, v_lAssignment_1533_);
lean_ctor_set(v_reuseFailAlloc_1552_, 7, v_eAssignment_1534_);
lean_ctor_set(v_reuseFailAlloc_1552_, 8, v_dAssignment_1535_);
v___x_1543_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1543_);
v___x_1545_ = v___x_1525_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_cache_1520_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_zetaDeltaFVarIds_1521_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_postponed_1522_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v_diag_1523_);
v___x_1545_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = lean_st_ref_set(v___y_1494_, v___x_1545_);
v___x_1547_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1547_);
v___x_1549_ = v___x_1516_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
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
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1511_);
lean_dec(v_index_1509_);
lean_dec(v_numScopeArgs_1508_);
lean_dec_ref(v_localInstances_1506_);
lean_dec(v_depth_1505_);
lean_dec_ref(v_type_1504_);
lean_dec(v_userName_1502_);
lean_dec(v_mvarId_1489_);
v_a_1557_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1513_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1513_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec(v___x_1500_);
lean_dec(v_idx_1490_);
v___x_1566_ = lean_obj_once(&l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1, &l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1_once, _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1);
v___x_1567_ = l_Lean_MessageData_ofName(v_mvarId_1489_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(v___x_1568_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___boxed(lean_object* v_mvarId_1570_, lean_object* v_idx_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_mvarId_1570_, v_idx_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC(lean_object* v_goal_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_initialCtxSize_1588_; lean_object* v___x_1589_; 
v_initialCtxSize_1588_ = lean_ctor_get(v_a_1581_, 5);
lean_inc(v_initialCtxSize_1588_);
lean_inc(v_goal_1580_);
v___x_1589_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_goal_1580_, v_initialCtxSize_1588_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref(v___x_1589_);
lean_inc(v_goal_1580_);
v___x_1590_ = l_Lean_MVarId_getType(v_goal_1580_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = 2;
lean_inc(v_goal_1580_);
v___x_1593_ = l_Lean_MVarId_setKind___redArg(v_goal_1580_, v___x_1592_, v_a_1584_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1636_; 
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; 
v_unused_1637_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1637_);
v___x_1595_ = v___x_1593_;
v_isShared_1596_ = v_isSharedCheck_1636_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v___x_1593_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1636_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v_env_1598_; uint8_t v___x_1599_; 
v___x_1597_ = lean_st_ref_get(v_a_1586_);
v_env_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc_ref(v_env_1598_);
lean_dec(v___x_1597_);
v___x_1599_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_1598_, v_a_1591_);
lean_dec(v_a_1591_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v_fuel_1601_; lean_object* v_simpState_1602_; lean_object* v_invariants_1603_; lean_object* v_vcs_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1617_; 
v___x_1600_ = lean_st_ref_take(v_a_1582_);
v_fuel_1601_ = lean_ctor_get(v___x_1600_, 0);
v_simpState_1602_ = lean_ctor_get(v___x_1600_, 1);
v_invariants_1603_ = lean_ctor_get(v___x_1600_, 2);
v_vcs_1604_ = lean_ctor_get(v___x_1600_, 3);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1606_ = v___x_1600_;
v_isShared_1607_ = v_isSharedCheck_1617_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_vcs_1604_);
lean_inc(v_invariants_1603_);
lean_inc(v_simpState_1602_);
lean_inc(v_fuel_1601_);
lean_dec(v___x_1600_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1617_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_array_push(v_vcs_1604_, v_goal_1580_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 3, v___x_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_fuel_1601_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_simpState_1602_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_invariants_1603_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1611_ = lean_st_ref_set(v_a_1582_, v___x_1610_);
v___x_1612_ = lean_box(0);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1612_);
v___x_1614_ = v___x_1595_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v_fuel_1619_; lean_object* v_simpState_1620_; lean_object* v_invariants_1621_; lean_object* v_vcs_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1635_; 
v___x_1618_ = lean_st_ref_take(v_a_1582_);
v_fuel_1619_ = lean_ctor_get(v___x_1618_, 0);
v_simpState_1620_ = lean_ctor_get(v___x_1618_, 1);
v_invariants_1621_ = lean_ctor_get(v___x_1618_, 2);
v_vcs_1622_ = lean_ctor_get(v___x_1618_, 3);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1624_ = v___x_1618_;
v_isShared_1625_ = v_isSharedCheck_1635_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_vcs_1622_);
lean_inc(v_invariants_1621_);
lean_inc(v_simpState_1620_);
lean_inc(v_fuel_1619_);
lean_dec(v___x_1618_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1635_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_array_push(v_invariants_1621_, v_goal_1580_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 2, v___x_1626_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_fuel_1619_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_simpState_1620_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_vcs_1622_);
v___x_1628_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = lean_st_ref_set(v_a_1582_, v___x_1628_);
v___x_1630_ = lean_box(0);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1630_);
v___x_1632_ = v___x_1595_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1591_);
lean_dec(v_goal_1580_);
return v___x_1593_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_goal_1580_);
v_a_1638_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1590_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1590_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_dec(v_goal_1580_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC___boxed(lean_object* v_goal_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v_goal_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1(lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_x_1656_, v_x_1657_, v_x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2(lean_object* v_00_u03b1_1660_, lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(v_msg_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2(v_00_u03b1_1668_, v_msg_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object* v_range_1676_, lean_object* v_b_1677_, lean_object* v_i_1678_, lean_object* v_hs_1679_, lean_object* v_hl_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_1676_, v_b_1677_, v_i_1678_, v___y_1685_, v___y_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object* v_range_1689_, lean_object* v_b_1690_, lean_object* v_i_1691_, lean_object* v_hs_1692_, lean_object* v_hl_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(v_range_1689_, v_b_1690_, v_i_1691_, v_hs_1692_, v_hl_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec_ref(v_range_1689_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1702_, lean_object* v_x_1703_, size_t v_x_1704_, size_t v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1703_, v_x_1704_, v_x_1705_, v_x_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
size_t v_x_8617__boxed_1715_; size_t v_x_8618__boxed_1716_; lean_object* v_res_1717_; 
v_x_8617__boxed_1715_ = lean_unbox_usize(v_x_1711_);
lean_dec(v_x_1711_);
v_x_8618__boxed_1716_ = lean_unbox_usize(v_x_1712_);
lean_dec(v_x_1712_);
v_res_1717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(v_00_u03b2_1709_, v_x_1710_, v_x_8617__boxed_1715_, v_x_8618__boxed_1716_, v_x_1713_, v_x_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1718_, lean_object* v_n_1719_, lean_object* v_k_1720_, lean_object* v_v_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v_n_1719_, v_k_1720_, v_v_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1723_, size_t v_depth_1724_, lean_object* v_keys_1725_, lean_object* v_vals_1726_, lean_object* v_heq_1727_, lean_object* v_i_1728_, lean_object* v_entries_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_1724_, v_keys_1725_, v_vals_1726_, v_i_1728_, v_entries_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1731_, lean_object* v_depth_1732_, lean_object* v_keys_1733_, lean_object* v_vals_1734_, lean_object* v_heq_1735_, lean_object* v_i_1736_, lean_object* v_entries_1737_){
_start:
{
size_t v_depth_boxed_1738_; lean_object* v_res_1739_; 
v_depth_boxed_1738_ = lean_unbox_usize(v_depth_1732_);
lean_dec(v_depth_1732_);
v_res_1739_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_1731_, v_depth_boxed_1738_, v_keys_1733_, v_vals_1734_, v_heq_1735_, v_i_1736_, v_entries_1737_);
lean_dec_ref(v_vals_1734_);
lean_dec_ref(v_keys_1733_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_x_1741_, v_x_1742_, v_x_1743_, v_x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC(lean_object* v_subGoal_1746_, lean_object* v_name_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_subGoal_1746_, v_name_1747_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_Expr_mvarId_x21(v_a_1756_);
v___x_1758_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v___x_1757_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1766_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_a_1756_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1756_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1756_);
v_a_1767_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1758_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1758_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC___boxed(lean_object* v_subGoal_1775_, lean_object* v_name_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Elab_Tactic_Do_emitVC(v_subGoal_1775_, v_name_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg(lean_object* v_x_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v_fuel_1794_; lean_object* v_simpState_1795_; lean_object* v_invariants_1796_; lean_object* v_vcs_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1820_; 
v___x_1793_ = lean_st_ref_get(v_a_1787_);
v_fuel_1794_ = lean_ctor_get(v___x_1793_, 0);
v_simpState_1795_ = lean_ctor_get(v___x_1793_, 1);
v_invariants_1796_ = lean_ctor_get(v___x_1793_, 2);
v_vcs_1797_ = lean_ctor_get(v___x_1793_, 3);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1799_ = v___x_1793_;
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_vcs_1797_);
lean_inc(v_invariants_1796_);
lean_inc(v_simpState_1795_);
lean_inc(v_fuel_1794_);
lean_dec(v___x_1793_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v_simpCtx_1802_; lean_object* v_simprocs_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1801_ = lean_st_mk_ref(v_simpState_1795_);
v_simpCtx_1802_ = lean_ctor_get(v_a_1786_, 2);
v_simprocs_1803_ = lean_ctor_get(v_a_1786_, 3);
lean_inc_ref(v_simprocs_1803_);
v___x_1804_ = l_Lean_Meta_Simp_mkDefaultMethodsCore(v_simprocs_1803_);
v___x_1805_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v___x_1804_);
lean_dec_ref(v___x_1804_);
lean_inc(v_a_1791_);
lean_inc_ref(v_a_1790_);
lean_inc(v_a_1789_);
lean_inc_ref(v_a_1788_);
lean_inc(v___x_1801_);
lean_inc_ref(v_simpCtx_1802_);
v___x_1806_ = lean_apply_8(v_x_1785_, v___x_1805_, v_simpCtx_1802_, v___x_1801_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, lean_box(0));
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1819_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1819_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1819_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_st_ref_get(v___x_1801_);
lean_dec(v___x_1801_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1811_);
v___x_1813_ = v___x_1799_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_fuel_1794_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_invariants_1796_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_vcs_1797_);
v___x_1813_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_st_ref_set(v_a_1787_, v___x_1813_);
if (v_isShared_1810_ == 0)
{
v___x_1816_ = v___x_1809_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1807_);
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
else
{
lean_dec(v___x_1801_);
lean_del_object(v___x_1799_);
lean_dec_ref(v_vcs_1797_);
lean_dec_ref(v_invariants_1796_);
lean_dec(v_fuel_1794_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg___boxed(lean_object* v_x_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM(lean_object* v_00_u03b1_1830_, lean_object* v_x_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_x_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Elab_Tactic_Do_liftSimpM(v_00_u03b1_1840_, v_x_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_object* v_00_u03b1_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(v_00_u03b1_1860_, v_x_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg(lean_object* v_jp_1872_, lean_object* v_info_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_config_1882_; lean_object* v_specThms_1883_; lean_object* v_simpCtx_1884_; lean_object* v_simprocs_1885_; lean_object* v_jps_1886_; lean_object* v_initialCtxSize_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_config_1882_ = lean_ctor_get(v_a_1875_, 0);
v_specThms_1883_ = lean_ctor_get(v_a_1875_, 1);
v_simpCtx_1884_ = lean_ctor_get(v_a_1875_, 2);
v_simprocs_1885_ = lean_ctor_get(v_a_1875_, 3);
v_jps_1886_ = lean_ctor_get(v_a_1875_, 4);
v_initialCtxSize_1887_ = lean_ctor_get(v_a_1875_, 5);
lean_inc(v_jps_1886_);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_1872_, v_info_1873_, v_jps_1886_);
lean_inc(v_initialCtxSize_1887_);
lean_inc_ref(v_simprocs_1885_);
lean_inc_ref(v_simpCtx_1884_);
lean_inc_ref(v_specThms_1883_);
lean_inc_ref(v_config_1882_);
v___x_1889_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1889_, 0, v_config_1882_);
lean_ctor_set(v___x_1889_, 1, v_specThms_1883_);
lean_ctor_set(v___x_1889_, 2, v_simpCtx_1884_);
lean_ctor_set(v___x_1889_, 3, v_simprocs_1885_);
lean_ctor_set(v___x_1889_, 4, v___x_1888_);
lean_ctor_set(v___x_1889_, 5, v_initialCtxSize_1887_);
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
lean_inc(v_a_1878_);
lean_inc_ref(v_a_1877_);
lean_inc(v_a_1876_);
v___x_1890_ = lean_apply_7(v_a_1874_, v___x_1889_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, lean_box(0));
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg___boxed(lean_object* v_jp_1891_, lean_object* v_info_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_1891_, v_info_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP(lean_object* v_00_u03b1_1902_, lean_object* v_jp_1903_, lean_object* v_info_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_1903_, v_info_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_jp_1915_, lean_object* v_info_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Elab_Tactic_Do_withJP(v_00_u03b1_1914_, v_jp_1915_, v_info_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(lean_object* v_t_1926_, lean_object* v_k_1927_){
_start:
{
if (lean_obj_tag(v_t_1926_) == 0)
{
lean_object* v_k_1928_; lean_object* v_v_1929_; lean_object* v_l_1930_; lean_object* v_r_1931_; uint8_t v___x_1932_; 
v_k_1928_ = lean_ctor_get(v_t_1926_, 1);
v_v_1929_ = lean_ctor_get(v_t_1926_, 2);
v_l_1930_ = lean_ctor_get(v_t_1926_, 3);
v_r_1931_ = lean_ctor_get(v_t_1926_, 4);
v___x_1932_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1927_, v_k_1928_);
switch(v___x_1932_)
{
case 0:
{
v_t_1926_ = v_l_1930_;
goto _start;
}
case 1:
{
lean_object* v___x_1934_; 
lean_inc(v_v_1929_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_v_1929_);
return v___x_1934_;
}
default: 
{
v_t_1926_ = v_r_1931_;
goto _start;
}
}
}
else
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_box(0);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_1937_, lean_object* v_k_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_1937_, v_k_1938_);
lean_dec(v_k_1938_);
lean_dec(v_t_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(lean_object* v_jp_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_jps_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_jps_1943_ = lean_ctor_get(v_a_1941_, 4);
v___x_1944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_jps_1943_, v_jp_1940_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg___boxed(lean_object* v_jp_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_1946_, v_a_1947_);
lean_dec_ref(v_a_1947_);
lean_dec(v_jp_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f(lean_object* v_jp_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_1950_, v_a_1951_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___boxed(lean_object* v_jp_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Elab_Tactic_Do_knownJP_x3f(v_jp_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_jp_1959_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(lean_object* v_00_u03b4_1968_, lean_object* v_t_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_1969_, v_k_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_1972_, lean_object* v_t_1973_, lean_object* v_k_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(v_00_u03b4_1972_, v_t_1973_, v_k_1974_);
lean_dec(v_k_1974_);
lean_dec(v_t_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isDuplicable(lean_object* v_e_1981_){
_start:
{
switch(lean_obj_tag(v_e_1981_))
{
case 5:
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isDuplicable___closed__2));
v___x_1983_ = l_Lean_Expr_isAppOf(v_e_1981_, v___x_1982_);
return v___x_1983_;
}
case 6:
{
uint8_t v___x_1984_; 
v___x_1984_ = 0;
return v___x_1984_;
}
case 7:
{
uint8_t v___x_1985_; 
v___x_1985_ = 0;
return v___x_1985_;
}
case 8:
{
uint8_t v___x_1986_; 
v___x_1986_ = 0;
return v___x_1986_;
}
case 10:
{
lean_object* v_expr_1987_; 
v_expr_1987_ = lean_ctor_get(v_e_1981_, 1);
v_e_1981_ = v_expr_1987_;
goto _start;
}
case 11:
{
lean_object* v_struct_1989_; 
v_struct_1989_ = lean_ctor_get(v_e_1981_, 2);
v_e_1981_ = v_struct_1989_;
goto _start;
}
default: 
{
uint8_t v___x_1991_; 
v___x_1991_ = 1;
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___boxed(lean_object* v_e_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_e_1992_);
lean_dec_ref(v_e_1992_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(lean_object* v_k_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
v___x_2004_ = lean_apply_8(v_k_1995_, v_b_1998_, v___y_1996_, v___y_1997_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, lean_box(0));
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed(lean_object* v_k_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(v_k_2005_, v___y_2006_, v___y_2007_, v_b_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(lean_object* v_name_2015_, lean_object* v_type_2016_, lean_object* v_val_2017_, lean_object* v_k_2018_, uint8_t v_nondep_2019_, uint8_t v_kind_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___f_2028_; lean_object* v___x_2029_; 
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2028_, 0, v_k_2018_);
lean_closure_set(v___f_2028_, 1, v___y_2021_);
lean_closure_set(v___f_2028_, 2, v___y_2022_);
v___x_2029_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2015_, v_type_2016_, v_val_2017_, v___f_2028_, v_nondep_2019_, v_kind_2020_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2029_) == 0)
{
return v___x_2029_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___boxed(lean_object* v_name_2038_, lean_object* v_type_2039_, lean_object* v_val_2040_, lean_object* v_k_2041_, lean_object* v_nondep_2042_, lean_object* v_kind_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_nondep_boxed_2051_; uint8_t v_kind_boxed_2052_; lean_object* v_res_2053_; 
v_nondep_boxed_2051_ = lean_unbox(v_nondep_2042_);
v_kind_boxed_2052_ = lean_unbox(v_kind_2043_);
v_res_2053_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2038_, v_type_2039_, v_val_2040_, v_k_2041_, v_nondep_boxed_2051_, v_kind_boxed_2052_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_object* v_00_u03b1_2054_, lean_object* v_name_2055_, lean_object* v_type_2056_, lean_object* v_val_2057_, lean_object* v_k_2058_, uint8_t v_nondep_2059_, uint8_t v_kind_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2055_, v_type_2056_, v_val_2057_, v_k_2058_, v_nondep_2059_, v_kind_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_name_2070_, lean_object* v_type_2071_, lean_object* v_val_2072_, lean_object* v_k_2073_, lean_object* v_nondep_2074_, lean_object* v_kind_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_nondep_boxed_2083_; uint8_t v_kind_boxed_2084_; lean_object* v_res_2085_; 
v_nondep_boxed_2083_ = lean_unbox(v_nondep_2074_);
v_kind_boxed_2084_ = lean_unbox(v_kind_2075_);
v_res_2085_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(v_00_u03b1_2069_, v_name_2070_, v_type_2071_, v_val_2072_, v_k_2073_, v_nondep_boxed_2083_, v_kind_boxed_2084_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(lean_object* v___x_2086_, lean_object* v_x_2087_, uint8_t v___x_2088_, uint8_t v___x_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Meta_mkLetFVars(v___x_2086_, v_x_2087_, v___x_2088_, v___x_2088_, v___x_2089_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed(lean_object* v___x_2099_, lean_object* v_x_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
uint8_t v___x_1593__boxed_2111_; uint8_t v___x_1594__boxed_2112_; lean_object* v_res_2113_; 
v___x_1593__boxed_2111_ = lean_unbox(v___x_2101_);
v___x_1594__boxed_2112_ = lean_unbox(v___x_2102_);
v_res_2113_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(v___x_2099_, v_x_2100_, v___x_1593__boxed_2111_, v___x_1594__boxed_2112_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___x_2099_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(lean_object* v_fv_2114_, uint8_t v___x_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; 
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_array_push(v___x_2125_, v_fv_2114_);
v___x_2127_ = 1;
v___x_2128_ = lean_box(v___x_2115_);
v___x_2129_ = lean_box(v___x_2127_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_2130_, 0, v___x_2126_);
lean_closure_set(v___f_2130_, 1, v_x_2116_);
lean_closure_set(v___f_2130_, 2, v___x_2128_);
lean_closure_set(v___f_2130_, 3, v___x_2129_);
v___x_2131_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_2130_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed(lean_object* v_fv_2132_, lean_object* v___x_2133_, lean_object* v_x_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v___x_1629__boxed_2142_; lean_object* v_res_2143_; 
v___x_1629__boxed_2142_ = lean_unbox(v___x_2133_);
v_res_2143_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(v_fv_2132_, v___x_1629__boxed_2142_, v_x_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(uint8_t v___x_2144_, lean_object* v_k_2145_, lean_object* v_fv_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = lean_box(v___x_2144_);
lean_inc_ref(v_fv_2146_);
v___f_2155_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2155_, 0, v_fv_2146_);
lean_closure_set(v___f_2155_, 1, v___x_2154_);
v___x_2156_ = lean_box(v___x_2144_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
v___x_2157_ = lean_apply_10(v_k_2145_, v___x_2156_, v_fv_2146_, v___f_2155_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, lean_box(0));
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed(lean_object* v___x_2158_, lean_object* v_k_2159_, lean_object* v_fv_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v___x_1672__boxed_2168_; lean_object* v_res_2169_; 
v___x_1672__boxed_2168_ = lean_unbox(v___x_2158_);
v_res_2169_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(v___x_1672__boxed_2168_, v_k_2159_, v_fv_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___y_2170_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed(lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(lean_object* v_name_2189_, lean_object* v_type_2190_, lean_object* v_val_2191_, lean_object* v_k_2192_, uint8_t v_kind_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_val_2191_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
v___x_2202_ = 1;
v___x_2203_ = lean_box(v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_2204_, 0, v___x_2203_);
lean_closure_set(v___f_2204_, 1, v_k_2192_);
v___x_2205_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2189_, v_type_2190_, v_val_2191_, v___f_2204_, v___x_2201_, v_kind_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2205_;
}
else
{
lean_object* v___f_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_type_2190_);
lean_dec(v_name_2189_);
v___f_2206_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0));
v___x_2207_ = 0;
v___x_2208_ = lean_box(v___x_2207_);
lean_inc(v_a_2199_);
lean_inc_ref(v_a_2198_);
lean_inc(v_a_2197_);
lean_inc_ref(v_a_2196_);
lean_inc(v_a_2195_);
lean_inc_ref(v_a_2194_);
v___x_2209_ = lean_apply_10(v_k_2192_, v___x_2208_, v_val_2191_, v___f_2206_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, lean_box(0));
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___boxed(lean_object* v_name_2210_, lean_object* v_type_2211_, lean_object* v_val_2212_, lean_object* v_k_2213_, lean_object* v_kind_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
uint8_t v_kind_boxed_2222_; lean_object* v_res_2223_; 
v_kind_boxed_2222_ = lean_unbox(v_kind_2214_);
v_res_2223_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2210_, v_type_2211_, v_val_2212_, v_k_2213_, v_kind_boxed_2222_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_object* v_00_u03b1_2224_, lean_object* v_name_2225_, lean_object* v_type_2226_, lean_object* v_val_2227_, lean_object* v_k_2228_, uint8_t v_kind_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2225_, v_type_2226_, v_val_2227_, v_k_2228_, v_kind_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_name_2239_, lean_object* v_type_2240_, lean_object* v_val_2241_, lean_object* v_k_2242_, lean_object* v_kind_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
uint8_t v_kind_boxed_2251_; lean_object* v_res_2252_; 
v_kind_boxed_2251_ = lean_unbox(v_kind_2243_);
v_res_2252_ = l_Lean_Elab_Tactic_Do_withLetDeclShared(v_00_u03b1_2238_, v_name_2239_, v_type_2240_, v_val_2241_, v_k_2242_, v_kind_boxed_2251_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2252_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object* v_n_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2257_ = lean_erase_macro_scopes(v_n_2256_);
v___x_2258_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isJP___closed__1));
v___x_2259_ = lean_name_eq(v___x_2257_, v___x_2258_);
lean_dec(v___x_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isJP___boxed(lean_object* v_n_2260_){
_start:
{
uint8_t v_res_2261_; lean_object* v_r_2262_; 
v_res_2261_ = l_Lean_Elab_Tactic_Do_isJP(v_n_2260_);
v_r_2262_ = lean_box(v_res_2261_);
return v_r_2262_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object* v_joinTy_2266_, lean_object* v_resTy_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Lean_Expr_isMData(v_joinTy_2266_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_expr_eqv(v_joinTy_2266_, v_resTy_2267_);
if (v___x_2274_ == 0)
{
uint8_t v___x_2275_; 
v___x_2275_ = l_Lean_Expr_isForall(v_joinTy_2266_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1, &l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1_once, _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1);
v___x_2277_ = l_Lean_MessageData_ofExpr(v_joinTy_2266_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_Lean_throwError___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__2___redArg(v___x_2278_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = l_Lean_Expr_consumeMData(v_joinTy_2266_);
lean_dec_ref(v_joinTy_2266_);
v___x_2281_ = l_Lean_Expr_bindingBody_x21(v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v___x_2281_, v_resTy_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2292_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2292_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2292_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_add(v___x_2287_, v_a_2283_);
lean_dec(v_a_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v_joinTy_2266_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Expr_consumeMData(v_joinTy_2266_);
lean_dec_ref(v_joinTy_2266_);
v_joinTy_2266_ = v___x_2295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___boxed(lean_object* v_joinTy_2297_, lean_object* v_resTy_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_joinTy_2297_, v_resTy_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v_resTy_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(lean_object* v_lastReduction_2306_, lean_object* v_f_2307_, lean_object* v_rargs_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
switch(lean_obj_tag(v_f_2307_))
{
case 10:
{
lean_object* v_expr_2314_; 
v_expr_2314_ = lean_ctor_get(v_f_2307_, 1);
lean_inc_ref(v_expr_2314_);
lean_dec_ref(v_f_2307_);
v_f_2307_ = v_expr_2314_;
goto _start;
}
case 5:
{
lean_object* v_fn_2316_; lean_object* v_arg_2317_; lean_object* v___x_2318_; 
v_fn_2316_ = lean_ctor_get(v_f_2307_, 0);
lean_inc_ref(v_fn_2316_);
v_arg_2317_ = lean_ctor_get(v_f_2307_, 1);
lean_inc_ref(v_arg_2317_);
lean_dec_ref(v_f_2307_);
v___x_2318_ = lean_array_push(v_rargs_2308_, v_arg_2317_);
v_f_2307_ = v_fn_2316_;
v_rargs_2308_ = v___x_2318_;
goto _start;
}
case 6:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2320_ = lean_array_get_size(v_rargs_2308_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_nat_dec_eq(v___x_2320_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v_e_x27_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v_lastReduction_2306_);
v_e_x27_2323_ = l_Lean_Expr_betaRev(v_f_2307_, v_rargs_2308_, v___x_2322_, v___x_2322_);
lean_dec_ref(v_rargs_2308_);
lean_inc_ref(v_e_x27_2323_);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_e_x27_2323_);
v___x_2325_ = l_Lean_Expr_getAppFn(v_e_x27_2323_);
v___x_2326_ = l_Lean_Expr_getAppNumArgs(v_e_x27_2323_);
v___x_2327_ = lean_mk_empty_array_with_capacity(v___x_2326_);
lean_dec(v___x_2326_);
v___x_2328_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_2323_, v___x_2327_);
v_lastReduction_2306_ = v___x_2324_;
v_f_2307_ = v___x_2325_;
v_rargs_2308_ = v___x_2328_;
goto _start;
}
else
{
lean_object* v___x_2330_; 
lean_dec_ref(v_f_2307_);
lean_dec_ref(v_rargs_2308_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_lastReduction_2306_);
return v___x_2330_;
}
}
case 4:
{
lean_object* v_declName_2331_; lean_object* v___x_2332_; lean_object* v_env_2333_; lean_object* v___x_2334_; 
v_declName_2331_ = lean_ctor_get(v_f_2307_, 0);
v___x_2332_ = lean_st_ref_get(v_a_2312_);
v_env_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_env_2333_);
lean_dec(v___x_2332_);
lean_inc(v_declName_2331_);
v___x_2334_ = l_Lean_Environment_getProjectionStructureName_x3f(v_env_2333_, v_declName_2331_);
if (lean_obj_tag(v___x_2334_) == 1)
{
lean_object* v_val_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2369_; 
v_val_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2369_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_val_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2369_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
if (lean_obj_tag(v_val_2335_) == 1)
{
lean_object* v_pre_2339_; 
v_pre_2339_ = lean_ctor_get(v_val_2335_, 0);
if (lean_obj_tag(v_pre_2339_) == 0)
{
lean_object* v_str_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_str_2340_ = lean_ctor_get(v_val_2335_, 1);
lean_inc_ref(v_str_2340_);
lean_dec_ref(v_val_2335_);
v___x_2341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0));
v___x_2342_ = lean_string_dec_eq(v_str_2340_, v___x_2341_);
lean_dec_ref(v_str_2340_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2344_; 
lean_dec_ref(v_f_2307_);
lean_dec_ref(v_rargs_2308_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 0);
lean_ctor_set(v___x_2337_, 0, v_lastReduction_2306_);
v___x_2344_ = v___x_2337_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_lastReduction_2306_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
else
{
lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
lean_del_object(v___x_2337_);
v___x_2346_ = l_Lean_mkAppRev(v_f_2307_, v_rargs_2308_);
lean_dec_ref(v_rargs_2308_);
v___x_2347_ = 0;
v___x_2348_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_2346_, v___x_2347_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2362_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2362_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2362_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
if (lean_obj_tag(v_a_2349_) == 0)
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_lastReduction_2306_);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_lastReduction_2306_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
lean_object* v_val_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_del_object(v___x_2351_);
v_val_2356_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_val_2356_);
lean_dec_ref(v_a_2349_);
v___x_2357_ = l_Lean_Expr_getAppFn(v_val_2356_);
v___x_2358_ = l_Lean_Expr_getAppNumArgs(v_val_2356_);
v___x_2359_ = lean_mk_empty_array_with_capacity(v___x_2358_);
lean_dec(v___x_2358_);
v___x_2360_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_val_2356_, v___x_2359_);
v_f_2307_ = v___x_2357_;
v_rargs_2308_ = v___x_2360_;
goto _start;
}
}
}
else
{
lean_dec(v_lastReduction_2306_);
return v___x_2348_;
}
}
}
else
{
lean_object* v___x_2364_; 
lean_dec_ref(v_val_2335_);
lean_dec_ref(v_f_2307_);
lean_dec_ref(v_rargs_2308_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 0);
lean_ctor_set(v___x_2337_, 0, v_lastReduction_2306_);
v___x_2364_ = v___x_2337_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_lastReduction_2306_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v___x_2367_; 
lean_dec(v_val_2335_);
lean_dec_ref(v_f_2307_);
lean_dec_ref(v_rargs_2308_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 0);
lean_ctor_set(v___x_2337_, 0, v_lastReduction_2306_);
v___x_2367_ = v___x_2337_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_lastReduction_2306_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v___x_2370_; 
lean_dec(v___x_2334_);
lean_dec_ref(v_f_2307_);
lean_dec_ref(v_rargs_2308_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_lastReduction_2306_);
return v___x_2370_;
}
}
case 11:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_reduceProj_x3f(v_f_2307_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2393_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2393_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2393_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
if (lean_obj_tag(v_a_2372_) == 0)
{
lean_object* v___x_2377_; 
lean_dec_ref(v_rargs_2308_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v_lastReduction_2306_);
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_lastReduction_2306_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2392_; 
lean_del_object(v___x_2374_);
lean_dec(v_lastReduction_2306_);
v_val_2379_ = lean_ctor_get(v_a_2372_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_a_2372_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2381_ = v_a_2372_;
v_isShared_2382_ = v_isSharedCheck_2392_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v_a_2372_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2392_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = l_Lean_mkAppRev(v_val_2379_, v_rargs_2308_);
lean_dec_ref(v_rargs_2308_);
lean_inc_ref(v___x_2383_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2386_ = l_Lean_Expr_getAppFn(v___x_2383_);
v___x_2387_ = l_Lean_Expr_getAppNumArgs(v___x_2383_);
v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2387_);
lean_dec(v___x_2387_);
v___x_2389_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2383_, v___x_2388_);
v_lastReduction_2306_ = v___x_2385_;
v_f_2307_ = v___x_2386_;
v_rargs_2308_ = v___x_2389_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v_rargs_2308_);
lean_dec(v_lastReduction_2306_);
return v___x_2371_;
}
}
case 8:
{
lean_object* v_declName_2394_; lean_object* v_type_2395_; lean_object* v_value_2396_; lean_object* v_body_2397_; uint8_t v_nondep_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_declName_2394_ = lean_ctor_get(v_f_2307_, 0);
lean_inc(v_declName_2394_);
v_type_2395_ = lean_ctor_get(v_f_2307_, 1);
lean_inc_ref(v_type_2395_);
v_value_2396_ = lean_ctor_get(v_f_2307_, 2);
lean_inc_ref(v_value_2396_);
v_body_2397_ = lean_ctor_get(v_f_2307_, 3);
lean_inc_ref(v_body_2397_);
v_nondep_2398_ = lean_ctor_get_uint8(v_f_2307_, sizeof(void*)*4 + 8);
lean_dec_ref(v_f_2307_);
v___x_2399_ = lean_box(0);
v___x_2400_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2399_, v_body_2397_, v_rargs_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2420_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2420_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2420_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
if (lean_obj_tag(v_a_2401_) == 0)
{
lean_object* v___x_2406_; 
lean_dec_ref(v_value_2396_);
lean_dec_ref(v_type_2395_);
lean_dec(v_declName_2394_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v_lastReduction_2306_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_lastReduction_2306_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
else
{
lean_object* v_val_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_lastReduction_2306_);
v_val_2408_ = lean_ctor_get(v_a_2401_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_a_2401_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v_a_2401_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_val_2408_);
lean_dec(v_a_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_Expr_letE___override(v_declName_2394_, v_type_2395_, v_value_2396_, v_val_2408_, v_nondep_2398_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2414_);
v___x_2416_ = v___x_2403_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_2396_);
lean_dec_ref(v_type_2395_);
lean_dec(v_declName_2394_);
lean_dec(v_lastReduction_2306_);
return v___x_2400_;
}
}
default: 
{
lean_object* v___x_2421_; 
lean_dec_ref(v_rargs_2308_);
lean_dec_ref(v_f_2307_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_lastReduction_2306_);
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___boxed(lean_object* v_lastReduction_2422_, lean_object* v_f_2423_, lean_object* v_rargs_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v_lastReduction_2422_, v_f_2423_, v_rargs_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(lean_object* v_e_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = l_Lean_Expr_getAppFn(v_e_2431_);
v___x_2439_ = l_Lean_Expr_getAppNumArgs(v_e_2431_);
v___x_2440_ = lean_mk_empty_array_with_capacity(v___x_2439_);
lean_dec(v___x_2439_);
v___x_2441_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_2431_, v___x_2440_);
v___x_2442_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2437_, v___x_2438_, v___x_2441_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f___boxed(lean_object* v_e_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(v_e_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
return v_res_2449_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg(){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___boxed(lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_object* v_00_u03b1_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___boxed(lean_object* v_00_u03b1_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(v_00_u03b1_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(lean_object* v_as_2480_, size_t v_sz_2481_, size_t v_i_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_a_2493_; uint8_t v___x_2497_; 
v___x_2497_ = lean_usize_dec_lt(v_i_2482_, v_sz_2481_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_b_2483_);
return v___x_2498_;
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_a_2499_ = lean_array_uget_borrowed(v_as_2480_, v_i_2482_);
lean_inc(v_a_2499_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2499_);
lean_inc_ref(v_b_2483_);
v___x_2501_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_b_2483_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2484_, v___y_2486_, v___y_2488_, v___y_2490_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_2499_);
v___x_2505_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_a_2499_, v___x_2504_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
lean_dec(v_a_2503_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_b_2483_, v_a_2506_);
v_a_2493_ = v___x_2507_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2528_; 
v_a_2508_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2510_ = v___x_2505_;
v_isShared_2511_ = v_isSharedCheck_2528_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2505_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2528_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
uint8_t v___y_2513_; uint8_t v___x_2526_; 
v___x_2526_ = l_Lean_Exception_isInterrupt(v_a_2508_);
if (v___x_2526_ == 0)
{
uint8_t v___x_2527_; 
lean_inc(v_a_2508_);
v___x_2527_ = l_Lean_Exception_isRuntime(v_a_2508_);
v___y_2513_ = v___x_2527_;
goto v___jp_2512_;
}
else
{
v___y_2513_ = v___x_2526_;
goto v___jp_2512_;
}
v___jp_2512_:
{
if (v___y_2513_ == 0)
{
lean_object* v___x_2514_; 
lean_del_object(v___x_2510_);
lean_dec(v_a_2508_);
v___x_2514_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2503_, v___y_2513_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref(v___x_2514_);
v_a_2493_ = v_b_2483_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v_b_2483_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v___x_2524_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_b_2483_);
if (v_isShared_2511_ == 0)
{
v___x_2524_ = v___x_2510_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2508_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec_ref(v_b_2483_);
v_a_2529_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2502_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2502_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
v_a_2493_ = v_b_2483_;
goto v___jp_2492_;
}
}
v___jp_2492_:
{
size_t v___x_2494_; size_t v___x_2495_; 
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2482_, v___x_2494_);
v_i_2482_ = v___x_2495_;
v_b_2483_ = v_a_2493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg___boxed(lean_object* v_as_2537_, lean_object* v_sz_2538_, lean_object* v_i_2539_, lean_object* v_b_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_sz_boxed_2549_; size_t v_i_boxed_2550_; lean_object* v_res_2551_; 
v_sz_boxed_2549_ = lean_unbox_usize(v_sz_2538_);
lean_dec(v_sz_2538_);
v_i_boxed_2550_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_2537_, v_sz_boxed_2549_, v_i_boxed_2550_, v_b_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v_as_2537_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_ref_2558_; lean_object* v___x_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2568_; 
v_ref_2558_ = lean_ctor_get(v___y_2555_, 5);
v___x_2559_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_elabConfig_spec__1_spec__4(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_inc(v_ref_2558_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_ref_2558_);
lean_ctor_set(v___x_2564_, 1, v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 1);
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg___boxed(lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(lean_object* v_ref_2576_, lean_object* v_msg_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_fileName_2587_; lean_object* v_fileMap_2588_; lean_object* v_options_2589_; lean_object* v_currRecDepth_2590_; lean_object* v_maxRecDepth_2591_; lean_object* v_ref_2592_; lean_object* v_currNamespace_2593_; lean_object* v_openDecls_2594_; lean_object* v_initHeartbeats_2595_; lean_object* v_maxHeartbeats_2596_; lean_object* v_quotContext_2597_; lean_object* v_currMacroScope_2598_; uint8_t v_diag_2599_; lean_object* v_cancelTk_x3f_2600_; uint8_t v_suppressElabErrors_2601_; lean_object* v_inheritedTraceOptions_2602_; lean_object* v_ref_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_fileName_2587_ = lean_ctor_get(v___y_2584_, 0);
v_fileMap_2588_ = lean_ctor_get(v___y_2584_, 1);
v_options_2589_ = lean_ctor_get(v___y_2584_, 2);
v_currRecDepth_2590_ = lean_ctor_get(v___y_2584_, 3);
v_maxRecDepth_2591_ = lean_ctor_get(v___y_2584_, 4);
v_ref_2592_ = lean_ctor_get(v___y_2584_, 5);
v_currNamespace_2593_ = lean_ctor_get(v___y_2584_, 6);
v_openDecls_2594_ = lean_ctor_get(v___y_2584_, 7);
v_initHeartbeats_2595_ = lean_ctor_get(v___y_2584_, 8);
v_maxHeartbeats_2596_ = lean_ctor_get(v___y_2584_, 9);
v_quotContext_2597_ = lean_ctor_get(v___y_2584_, 10);
v_currMacroScope_2598_ = lean_ctor_get(v___y_2584_, 11);
v_diag_2599_ = lean_ctor_get_uint8(v___y_2584_, sizeof(void*)*14);
v_cancelTk_x3f_2600_ = lean_ctor_get(v___y_2584_, 12);
v_suppressElabErrors_2601_ = lean_ctor_get_uint8(v___y_2584_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2602_ = lean_ctor_get(v___y_2584_, 13);
v_ref_2603_ = l_Lean_replaceRef(v_ref_2576_, v_ref_2592_);
lean_inc_ref(v_inheritedTraceOptions_2602_);
lean_inc(v_cancelTk_x3f_2600_);
lean_inc(v_currMacroScope_2598_);
lean_inc(v_quotContext_2597_);
lean_inc(v_maxHeartbeats_2596_);
lean_inc(v_initHeartbeats_2595_);
lean_inc(v_openDecls_2594_);
lean_inc(v_currNamespace_2593_);
lean_inc(v_maxRecDepth_2591_);
lean_inc(v_currRecDepth_2590_);
lean_inc_ref(v_options_2589_);
lean_inc_ref(v_fileMap_2588_);
lean_inc_ref(v_fileName_2587_);
v___x_2604_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2604_, 0, v_fileName_2587_);
lean_ctor_set(v___x_2604_, 1, v_fileMap_2588_);
lean_ctor_set(v___x_2604_, 2, v_options_2589_);
lean_ctor_set(v___x_2604_, 3, v_currRecDepth_2590_);
lean_ctor_set(v___x_2604_, 4, v_maxRecDepth_2591_);
lean_ctor_set(v___x_2604_, 5, v_ref_2603_);
lean_ctor_set(v___x_2604_, 6, v_currNamespace_2593_);
lean_ctor_set(v___x_2604_, 7, v_openDecls_2594_);
lean_ctor_set(v___x_2604_, 8, v_initHeartbeats_2595_);
lean_ctor_set(v___x_2604_, 9, v_maxHeartbeats_2596_);
lean_ctor_set(v___x_2604_, 10, v_quotContext_2597_);
lean_ctor_set(v___x_2604_, 11, v_currMacroScope_2598_);
lean_ctor_set(v___x_2604_, 12, v_cancelTk_x3f_2600_);
lean_ctor_set(v___x_2604_, 13, v_inheritedTraceOptions_2602_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*14, v_diag_2599_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*14 + 1, v_suppressElabErrors_2601_);
v___x_2605_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_2577_, v___y_2582_, v___y_2583_, v___x_2604_, v___y_2585_);
lean_dec_ref(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_ref_2606_, lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_2606_, v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v_ref_2606_);
return v_res_2617_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
lean_ctor_set(v___x_2623_, 2, v___x_2622_);
lean_ctor_set(v___x_2623_, 3, v___x_2621_);
lean_ctor_set(v___x_2623_, 4, v___x_2621_);
lean_ctor_set(v___x_2623_, 5, v___x_2621_);
lean_ctor_set(v___x_2623_, 6, v___x_2621_);
lean_ctor_set(v___x_2623_, 7, v___x_2621_);
lean_ctor_set(v___x_2623_, 8, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_unsigned_to_nat(32u);
v___x_2625_ = lean_mk_empty_array_with_capacity(v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2627_ = ((size_t)5ULL);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_unsigned_to_nat(32u);
v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
v___x_2631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3);
v___x_2632_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
lean_ctor_set(v___x_2632_, 1, v___x_2630_);
lean_ctor_set(v___x_2632_, 2, v___x_2628_);
lean_ctor_set(v___x_2632_, 3, v___x_2628_);
lean_ctor_set_usize(v___x_2632_, 4, v___x_2627_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2633_ = lean_box(1);
v___x_2634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_2635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_2636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v___x_2633_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6));
v___x_2639_ = l_Lean_stringToMessageData(v___x_2638_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_2658_, lean_object* v_declHint_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v_env_2663_; uint8_t v___x_2664_; 
v___x_2662_ = lean_st_ref_get(v___y_2660_);
v_env_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_ref(v_env_2663_);
lean_dec(v___x_2662_);
v___x_2664_ = l_Lean_Name_isAnonymous(v_declHint_2659_);
if (v___x_2664_ == 0)
{
uint8_t v_isExporting_2665_; 
v_isExporting_2665_ = lean_ctor_get_uint8(v_env_2663_, sizeof(void*)*8);
if (v_isExporting_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref(v_env_2663_);
lean_dec(v_declHint_2659_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_msg_2658_);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
lean_inc_ref(v_env_2663_);
v___x_2667_ = l_Lean_Environment_setExporting(v_env_2663_, v___x_2664_);
lean_inc(v_declHint_2659_);
lean_inc_ref(v___x_2667_);
v___x_2668_ = l_Lean_Environment_contains(v___x_2667_, v_declHint_2659_, v_isExporting_2665_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v___x_2667_);
lean_dec_ref(v_env_2663_);
lean_dec(v_declHint_2659_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_msg_2658_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_c_2675_; lean_object* v___x_2676_; 
v___x_2670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_2671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5);
v___x_2672_ = l_Lean_Options_empty;
v___x_2673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2667_);
lean_ctor_set(v___x_2673_, 1, v___x_2670_);
lean_ctor_set(v___x_2673_, 2, v___x_2671_);
lean_ctor_set(v___x_2673_, 3, v___x_2672_);
lean_inc(v_declHint_2659_);
v___x_2674_ = l_Lean_MessageData_ofConstName(v_declHint_2659_, v___x_2664_);
v_c_2675_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2675_, 0, v___x_2673_);
lean_ctor_set(v_c_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2663_, v_declHint_2659_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v_env_2663_);
lean_dec(v_declHint_2659_);
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v_c_2675_);
v___x_2679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_MessageData_note(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_msg_2658_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
else
{
lean_object* v_val_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2719_; 
v_val_2684_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2686_ = v___x_2676_;
v_isShared_2687_ = v_isSharedCheck_2719_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_val_2684_);
lean_dec(v___x_2676_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2719_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_mod_2691_; uint8_t v___x_2692_; 
v___x_2688_ = lean_box(0);
v___x_2689_ = l_Lean_Environment_header(v_env_2663_);
lean_dec_ref(v_env_2663_);
v___x_2690_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2689_);
v_mod_2691_ = lean_array_get(v___x_2688_, v___x_2690_, v_val_2684_);
lean_dec(v_val_2684_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l_Lean_isPrivateName(v_declHint_2659_);
lean_dec(v_declHint_2659_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_c_2675_);
v___x_2695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_MessageData_ofName(v_mod_2691_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_MessageData_note(v___x_2700_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_msg_2658_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set_tag(v___x_2686_, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2702_);
v___x_2704_ = v___x_2686_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v_c_2675_);
v___x_2708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_MessageData_ofName(v_mod_2691_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_note(v___x_2713_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_msg_2658_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set_tag(v___x_2686_, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2715_);
v___x_2717_ = v___x_2686_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2720_; 
lean_dec_ref(v_env_2663_);
lean_dec(v_declHint_2659_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_msg_2658_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_2721_, lean_object* v_declHint_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_2721_, v_declHint_2722_, v___y_2723_);
lean_dec(v___y_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(lean_object* v_msg_2726_, lean_object* v_declHint_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
v___x_2737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_2726_, v_declHint_2727_, v___y_2735_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2742_ = l_Lean_unknownIdentifierMessageTag;
v___x_2743_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v_a_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_2760_, lean_object* v_msg_2761_, lean_object* v_declHint_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; lean_object* v_a_2773_; lean_object* v___x_2774_; 
v___x_2772_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_2761_, v_declHint_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2772_);
v___x_2774_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_2760_, v_a_2773_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_2775_, lean_object* v_msg_2776_, lean_object* v_declHint_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_2775_, v_msg_2776_, v_declHint_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v_ref_2775_);
return v_res_2787_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__2));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(lean_object* v_ref_2794_, lean_object* v_constName_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___x_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2805_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1);
v___x_2806_ = 0;
lean_inc(v_constName_2795_);
v___x_2807_ = l_Lean_MessageData_ofConstName(v_constName_2795_, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2805_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_2794_, v___x_2810_, v_constName_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___boxed(lean_object* v_ref_2812_, lean_object* v_constName_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_2812_, v_constName_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v_ref_2812_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(lean_object* v_constName_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_ref_2834_; lean_object* v___x_2835_; 
v_ref_2834_ = lean_ctor_get(v___y_2831_, 5);
v___x_2835_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_2834_, v_constName_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg___boxed(lean_object* v_constName_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(lean_object* v_fst_2847_, lean_object* v_fst_2848_, lean_object* v_specThm_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_proof_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_proof_2859_ = lean_ctor_get(v_specThm_2849_, 2);
lean_inc_ref(v_proof_2859_);
lean_dec_ref(v_specThm_2849_);
v___x_2860_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(v_fst_2847_, v_proof_2859_);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v_fst_2848_);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0___boxed(lean_object* v_fst_2865_, lean_object* v_fst_2866_, lean_object* v_specThm_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_2865_, v_fst_2866_, v_specThm_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(lean_object* v_constName_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; lean_object* v_env_2889_; uint8_t v___x_2890_; lean_object* v___x_2891_; 
v___x_2888_ = lean_st_ref_get(v___y_2886_);
v_env_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc_ref(v_env_2889_);
lean_dec(v___x_2888_);
v___x_2890_ = 0;
lean_inc(v_constName_2878_);
v___x_2891_ = l_Lean_Environment_find_x3f(v_env_2889_, v_constName_2878_, v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2892_;
}
else
{
lean_object* v_val_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_constName_2878_);
v_val_2893_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2891_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_val_2893_);
lean_dec(v___x_2891_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 0);
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_val_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2___boxed(lean_object* v_constName_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_constName_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2911_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7));
v___x_2933_ = l_Lean_stringToMessageData(v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(lean_object* v_as_2935_, size_t v_sz_2936_, size_t v_i_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_a_2949_; uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_lt(v_i_2937_, v_sz_2936_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_b_2938_);
return v___x_2954_;
}
else
{
lean_object* v_snd_2955_; lean_object* v_fst_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3276_; 
v_snd_2955_ = lean_ctor_get(v_b_2938_, 1);
v_fst_2956_ = lean_ctor_get(v_b_2938_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_b_2938_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_2958_ = v_b_2938_;
v_isShared_2959_ = v_isSharedCheck_3276_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snd_2955_);
lean_inc(v_fst_2956_);
lean_dec(v_b_2938_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3276_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3275_; 
v_fst_2960_ = lean_ctor_get(v_snd_2955_, 0);
v_snd_2961_ = lean_ctor_get(v_snd_2955_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_snd_2955_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_2963_ = v_snd_2955_;
v_isShared_2964_ = v_isSharedCheck_3275_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snd_2961_);
lean_inc(v_fst_2960_);
lean_dec(v_snd_2955_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3275_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_fst_2966_; lean_object* v_snd_2967_; lean_object* v_fst_2975_; lean_object* v_snd_2976_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___y_2991_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_3006_; lean_object* v___y_3007_; uint8_t v___y_3008_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_2984_ = lean_unsigned_to_nat(1u);
v_a_2985_ = lean_array_uget_borrowed(v_as_2935_, v_i_2937_);
lean_inc(v_a_2985_);
v___x_3020_ = l_Lean_Syntax_getKind(v_a_2985_);
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2));
v___x_3022_ = lean_name_eq(v___x_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4));
v___x_3024_ = lean_name_eq(v___x_3020_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; uint8_t v___x_3026_; 
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
v___x_3025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6));
v___x_3026_ = lean_name_eq(v___x_3020_, v___x_3025_);
lean_dec(v___x_3020_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref(v___x_3027_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v_fst_2960_);
lean_ctor_set(v___x_3028_, 1, v_snd_2961_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v_fst_2956_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v_a_2949_ = v___x_3029_;
goto v___jp_2948_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3030_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3027_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3027_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec(v_snd_2961_);
lean_inc(v_a_2985_);
v___x_3038_ = lean_array_push(v_fst_2960_, v_a_2985_);
v___x_3039_ = lean_box(v___x_2953_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_fst_2956_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v_a_2949_ = v___x_3041_;
goto v___jp_2948_;
}
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
lean_dec(v___x_3020_);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = l_Lean_Syntax_getArg(v_a_2985_, v___x_3042_);
v___x_3044_ = l_Lean_Syntax_isNone(v___x_3043_);
lean_dec(v___x_3043_);
if (v___x_3044_ == 0)
{
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
goto v___jp_2986_;
}
else
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = l_Lean_Syntax_getArg(v_a_2985_, v___x_2984_);
v___x_3046_ = l_Lean_Syntax_isNone(v___x_3045_);
lean_dec(v___x_3045_);
if (v___x_3046_ == 0)
{
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
goto v___jp_2986_;
}
else
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Meta_saveState___redArg(v___y_2944_, v___y_2946_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3091_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_unsigned_to_nat(2u);
v___x_3050_ = l_Lean_Syntax_getArg(v_a_2985_, v___x_3049_);
v___x_3156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9));
lean_inc(v___x_3050_);
v___x_3157_ = l_Lean_Elab_Term_resolveId_x3f(v___x_3050_, v___x_3156_, v___x_2953_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_dec(v_a_3048_);
v___y_3091_ = v___x_3157_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3158_; uint8_t v___y_3160_; uint8_t v___x_3171_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
v___x_3171_ = l_Lean_Exception_isInterrupt(v_a_3158_);
if (v___x_3171_ == 0)
{
uint8_t v___x_3172_; 
v___x_3172_ = l_Lean_Exception_isRuntime(v_a_3158_);
v___y_3160_ = v___x_3172_;
goto v___jp_3159_;
}
else
{
lean_dec(v_a_3158_);
v___y_3160_ = v___x_3171_;
goto v___jp_3159_;
}
v___jp_3159_:
{
if (v___y_3160_ == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v___x_3157_);
v___x_3161_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3048_, v___y_2944_, v___y_2946_);
lean_dec(v_a_3048_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3162_; 
lean_dec_ref(v___x_3161_);
lean_inc(v___x_3050_);
v___x_3162_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_3050_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
v___y_3091_ = v___x_3162_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v___x_3050_);
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3163_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3161_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3161_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_dec(v_a_3048_);
v___y_3091_ = v___x_3157_;
goto v___jp_3090_;
}
}
}
v___jp_3051_:
{
lean_object* v_fileName_3056_; lean_object* v_fileMap_3057_; lean_object* v_options_3058_; lean_object* v_currRecDepth_3059_; lean_object* v_maxRecDepth_3060_; lean_object* v_ref_3061_; lean_object* v_currNamespace_3062_; lean_object* v_openDecls_3063_; lean_object* v_initHeartbeats_3064_; lean_object* v_maxHeartbeats_3065_; lean_object* v_quotContext_3066_; lean_object* v_currMacroScope_3067_; uint8_t v_diag_3068_; lean_object* v_cancelTk_x3f_3069_; uint8_t v_suppressElabErrors_3070_; lean_object* v_inheritedTraceOptions_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v_ref_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_fileName_3056_ = lean_ctor_get(v___y_3054_, 0);
v_fileMap_3057_ = lean_ctor_get(v___y_3054_, 1);
v_options_3058_ = lean_ctor_get(v___y_3054_, 2);
v_currRecDepth_3059_ = lean_ctor_get(v___y_3054_, 3);
v_maxRecDepth_3060_ = lean_ctor_get(v___y_3054_, 4);
v_ref_3061_ = lean_ctor_get(v___y_3054_, 5);
v_currNamespace_3062_ = lean_ctor_get(v___y_3054_, 6);
v_openDecls_3063_ = lean_ctor_get(v___y_3054_, 7);
v_initHeartbeats_3064_ = lean_ctor_get(v___y_3054_, 8);
v_maxHeartbeats_3065_ = lean_ctor_get(v___y_3054_, 9);
v_quotContext_3066_ = lean_ctor_get(v___y_3054_, 10);
v_currMacroScope_3067_ = lean_ctor_get(v___y_3054_, 11);
v_diag_3068_ = lean_ctor_get_uint8(v___y_3054_, sizeof(void*)*14);
v_cancelTk_x3f_3069_ = lean_ctor_get(v___y_3054_, 12);
v_suppressElabErrors_3070_ = lean_ctor_get_uint8(v___y_3054_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3071_ = lean_ctor_get(v___y_3054_, 13);
v___x_3072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8);
lean_inc(v___x_3050_);
v___x_3073_ = l_Lean_MessageData_ofSyntax(v___x_3050_);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__3);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v_ref_3077_ = l_Lean_replaceRef(v___x_3050_, v_ref_3061_);
lean_dec(v___x_3050_);
lean_inc_ref(v_inheritedTraceOptions_3071_);
lean_inc(v_cancelTk_x3f_3069_);
lean_inc(v_currMacroScope_3067_);
lean_inc(v_quotContext_3066_);
lean_inc(v_maxHeartbeats_3065_);
lean_inc(v_initHeartbeats_3064_);
lean_inc(v_openDecls_3063_);
lean_inc(v_currNamespace_3062_);
lean_inc(v_maxRecDepth_3060_);
lean_inc(v_currRecDepth_3059_);
lean_inc_ref(v_options_3058_);
lean_inc_ref(v_fileMap_3057_);
lean_inc_ref(v_fileName_3056_);
v___x_3078_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3078_, 0, v_fileName_3056_);
lean_ctor_set(v___x_3078_, 1, v_fileMap_3057_);
lean_ctor_set(v___x_3078_, 2, v_options_3058_);
lean_ctor_set(v___x_3078_, 3, v_currRecDepth_3059_);
lean_ctor_set(v___x_3078_, 4, v_maxRecDepth_3060_);
lean_ctor_set(v___x_3078_, 5, v_ref_3077_);
lean_ctor_set(v___x_3078_, 6, v_currNamespace_3062_);
lean_ctor_set(v___x_3078_, 7, v_openDecls_3063_);
lean_ctor_set(v___x_3078_, 8, v_initHeartbeats_3064_);
lean_ctor_set(v___x_3078_, 9, v_maxHeartbeats_3065_);
lean_ctor_set(v___x_3078_, 10, v_quotContext_3066_);
lean_ctor_set(v___x_3078_, 11, v_currMacroScope_3067_);
lean_ctor_set(v___x_3078_, 12, v_cancelTk_x3f_3069_);
lean_ctor_set(v___x_3078_, 13, v_inheritedTraceOptions_3071_);
lean_ctor_set_uint8(v___x_3078_, sizeof(void*)*14, v_diag_3068_);
lean_ctor_set_uint8(v___x_3078_, sizeof(void*)*14 + 1, v_suppressElabErrors_3070_);
v___x_3079_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v___x_3076_, v___y_3052_, v___y_3053_, v___x_3078_, v___y_3055_);
lean_dec_ref(v___x_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v___x_3079_);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v_fst_2960_);
lean_ctor_set(v___x_3080_, 1, v_snd_2961_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_fst_2956_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v_a_2949_ = v___x_3081_;
goto v___jp_2948_;
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3082_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3079_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3079_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
v___jp_3090_:
{
if (lean_obj_tag(v___y_3091_) == 0)
{
lean_object* v_a_3092_; 
v_a_3092_ = lean_ctor_get(v___y_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref(v___y_3091_);
if (lean_obj_tag(v_a_3092_) == 1)
{
lean_object* v_val_3093_; 
v_val_3093_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_val_3093_);
lean_dec_ref(v_a_3092_);
switch(lean_obj_tag(v_val_3093_))
{
case 4:
{
lean_object* v_declName_3094_; lean_object* v___x_3095_; 
lean_dec(v___x_3050_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
v_declName_3094_ = lean_ctor_get(v_val_3093_, 0);
lean_inc_n(v_declName_3094_, 2);
lean_dec_ref(v_val_3093_);
v___x_3095_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_declName_3094_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v___x_3096_; 
lean_dec_ref(v___x_3095_);
v___x_3096_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2940_, v___y_2942_, v___y_2944_, v___y_2946_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref(v___x_3096_);
v___x_3098_ = lean_unsigned_to_nat(1000u);
v___x_3099_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_3094_, v___x_3098_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; 
lean_dec(v_a_3097_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref(v___x_3099_);
v___x_3101_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_2956_, v_a_3100_);
v_fst_2975_ = v___x_3101_;
v_snd_2976_ = v_fst_2960_;
goto v___jp_2974_;
}
else
{
lean_object* v_a_3102_; uint8_t v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3099_);
v___x_3103_ = l_Lean_Exception_isInterrupt(v_a_3102_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; 
lean_inc(v_a_3102_);
v___x_3104_ = l_Lean_Exception_isRuntime(v_a_3102_);
v___y_2991_ = v_a_3102_;
v___y_2992_ = v_a_3097_;
v___y_2993_ = v___x_3104_;
goto v___jp_2990_;
}
else
{
v___y_2991_ = v_a_3102_;
v___y_2992_ = v_a_3097_;
v___y_2993_ = v___x_3103_;
goto v___jp_2990_;
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_declName_3094_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3105_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3096_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3096_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_declName_3094_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3113_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3095_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3095_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3121_; lean_object* v___x_3122_; 
lean_dec(v___x_3050_);
v_fvarId_3121_ = lean_ctor_get(v_val_3093_, 0);
lean_inc(v_fvarId_3121_);
v___x_3122_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_val_3093_, v___y_2943_, v___y_2945_, v___y_2946_);
lean_dec_ref(v_val_3093_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v___x_3122_);
v___x_3123_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2940_, v___y_2942_, v___y_2944_, v___y_2946_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = lean_unsigned_to_nat(1000u);
v___x_3126_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_3121_, v___x_3125_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; 
lean_dec(v_a_3124_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_2956_, v_a_3127_);
v_fst_2966_ = v___x_3128_;
v_snd_2967_ = v_fst_2960_;
goto v___jp_2965_;
}
else
{
lean_object* v_a_3129_; uint8_t v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3129_);
lean_dec_ref(v___x_3126_);
v___x_3130_ = l_Lean_Exception_isInterrupt(v_a_3129_);
if (v___x_3130_ == 0)
{
uint8_t v___x_3131_; 
lean_inc(v_a_3129_);
v___x_3131_ = l_Lean_Exception_isRuntime(v_a_3129_);
v___y_3006_ = v_a_3129_;
v___y_3007_ = v_a_3124_;
v___y_3008_ = v___x_3131_;
goto v___jp_3005_;
}
else
{
v___y_3006_ = v_a_3129_;
v___y_3007_ = v_a_3124_;
v___y_3008_ = v___x_3130_;
goto v___jp_3005_;
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_fvarId_3121_);
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3132_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3123_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3123_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_fvarId_3121_);
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3140_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3122_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3122_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
default: 
{
lean_dec(v_val_3093_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
v___y_3052_ = v___y_2943_;
v___y_3053_ = v___y_2944_;
v___y_3054_ = v___y_2945_;
v___y_3055_ = v___y_2946_;
goto v___jp_3051_;
}
}
}
else
{
lean_dec(v_a_3092_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
v___y_3052_ = v___y_2943_;
v___y_3053_ = v___y_2944_;
v___y_3054_ = v___y_2945_;
v___y_3055_ = v___y_2946_;
goto v___jp_3051_;
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v___x_3050_);
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3148_ = lean_ctor_get(v___y_3091_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___y_3091_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___y_3091_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___y_3091_);
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
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3173_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3047_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3047_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3181_; 
lean_dec(v___x_3020_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
v___x_3181_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2940_, v___y_2942_, v___y_2944_, v___y_2946_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3266_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3266_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3266_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v_a_3203_; lean_object* v___y_3207_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = l_Lean_Syntax_getArg(v_a_2985_, v___x_2984_);
lean_inc(v___x_3213_);
v___x_3214_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_3213_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
if (lean_obj_tag(v_a_3215_) == 1)
{
lean_object* v_val_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v___x_3213_);
v_val_3216_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_val_3216_);
lean_dec_ref(v_a_3215_);
v___x_3217_ = l_Lean_Expr_fvarId_x21(v_val_3216_);
lean_dec(v_val_3216_);
v___x_3218_ = lean_unsigned_to_nat(1000u);
v___x_3219_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_3217_, v___x_3218_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3219_);
lean_inc(v_fst_2960_);
lean_inc(v_fst_2956_);
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_2956_, v_fst_2960_, v_a_3220_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
v___y_3207_ = v___x_3221_;
goto v___jp_3206_;
}
else
{
lean_object* v_a_3222_; 
v_a_3222_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3219_);
v_a_3203_ = v_a_3222_;
goto v___jp_3202_;
}
}
else
{
lean_object* v___x_3223_; 
lean_dec(v_a_3215_);
v___x_3223_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2940_, v___y_2942_, v___y_2944_, v___y_2946_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = lean_box(0);
lean_inc(v___x_3213_);
v___x_3226_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_3213_, v___x_3225_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec(v_a_3224_);
lean_dec(v___x_3213_);
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3226_);
v___x_3228_ = lean_unsigned_to_nat(1000u);
v___x_3229_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_a_3227_, v___x_3228_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
lean_inc(v_fst_2960_);
lean_inc(v_fst_2956_);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_2956_, v_fst_2960_, v_a_3230_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
v___y_3207_ = v___x_3231_;
goto v___jp_3206_;
}
else
{
lean_object* v_a_3232_; 
v_a_3232_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3229_);
v_a_3203_ = v_a_3232_;
goto v___jp_3202_;
}
}
else
{
lean_object* v_a_3233_; uint8_t v___y_3235_; uint8_t v___x_3262_; 
v_a_3233_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3233_);
lean_dec_ref(v___x_3226_);
v___x_3262_ = l_Lean_Exception_isInterrupt(v_a_3233_);
if (v___x_3262_ == 0)
{
uint8_t v___x_3263_; 
lean_inc(v_a_3233_);
v___x_3263_ = l_Lean_Exception_isRuntime(v_a_3233_);
v___y_3235_ = v___x_3263_;
goto v___jp_3234_;
}
else
{
v___y_3235_ = v___x_3262_;
goto v___jp_3234_;
}
v___jp_3234_:
{
if (v___y_3235_ == 0)
{
lean_object* v___x_3236_; 
lean_dec(v_a_3233_);
v___x_3236_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3224_, v___y_3235_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_fileName_3237_; lean_object* v_fileMap_3238_; lean_object* v_options_3239_; lean_object* v_currRecDepth_3240_; lean_object* v_maxRecDepth_3241_; lean_object* v_ref_3242_; lean_object* v_currNamespace_3243_; lean_object* v_openDecls_3244_; lean_object* v_initHeartbeats_3245_; lean_object* v_maxHeartbeats_3246_; lean_object* v_quotContext_3247_; lean_object* v_currMacroScope_3248_; uint8_t v_diag_3249_; lean_object* v_cancelTk_x3f_3250_; uint8_t v_suppressElabErrors_3251_; lean_object* v_inheritedTraceOptions_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_ref_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec_ref(v___x_3236_);
v_fileName_3237_ = lean_ctor_get(v___y_2945_, 0);
v_fileMap_3238_ = lean_ctor_get(v___y_2945_, 1);
v_options_3239_ = lean_ctor_get(v___y_2945_, 2);
v_currRecDepth_3240_ = lean_ctor_get(v___y_2945_, 3);
v_maxRecDepth_3241_ = lean_ctor_get(v___y_2945_, 4);
v_ref_3242_ = lean_ctor_get(v___y_2945_, 5);
v_currNamespace_3243_ = lean_ctor_get(v___y_2945_, 6);
v_openDecls_3244_ = lean_ctor_get(v___y_2945_, 7);
v_initHeartbeats_3245_ = lean_ctor_get(v___y_2945_, 8);
v_maxHeartbeats_3246_ = lean_ctor_get(v___y_2945_, 9);
v_quotContext_3247_ = lean_ctor_get(v___y_2945_, 10);
v_currMacroScope_3248_ = lean_ctor_get(v___y_2945_, 11);
v_diag_3249_ = lean_ctor_get_uint8(v___y_2945_, sizeof(void*)*14);
v_cancelTk_x3f_3250_ = lean_ctor_get(v___y_2945_, 12);
v_suppressElabErrors_3251_ = lean_ctor_get_uint8(v___y_2945_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3252_ = lean_ctor_get(v___y_2945_, 13);
v___x_3253_ = l_Lean_Syntax_getId(v___x_3213_);
v___x_3254_ = lean_erase_macro_scopes(v___x_3253_);
v_ref_3255_ = l_Lean_replaceRef(v___x_3213_, v_ref_3242_);
lean_dec(v___x_3213_);
lean_inc_ref(v_inheritedTraceOptions_3252_);
lean_inc(v_cancelTk_x3f_3250_);
lean_inc(v_currMacroScope_3248_);
lean_inc(v_quotContext_3247_);
lean_inc(v_maxHeartbeats_3246_);
lean_inc(v_initHeartbeats_3245_);
lean_inc(v_openDecls_3244_);
lean_inc(v_currNamespace_3243_);
lean_inc(v_maxRecDepth_3241_);
lean_inc(v_currRecDepth_3240_);
lean_inc_ref(v_options_3239_);
lean_inc_ref(v_fileMap_3238_);
lean_inc_ref(v_fileName_3237_);
v___x_3256_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3256_, 0, v_fileName_3237_);
lean_ctor_set(v___x_3256_, 1, v_fileMap_3238_);
lean_ctor_set(v___x_3256_, 2, v_options_3239_);
lean_ctor_set(v___x_3256_, 3, v_currRecDepth_3240_);
lean_ctor_set(v___x_3256_, 4, v_maxRecDepth_3241_);
lean_ctor_set(v___x_3256_, 5, v_ref_3255_);
lean_ctor_set(v___x_3256_, 6, v_currNamespace_3243_);
lean_ctor_set(v___x_3256_, 7, v_openDecls_3244_);
lean_ctor_set(v___x_3256_, 8, v_initHeartbeats_3245_);
lean_ctor_set(v___x_3256_, 9, v_maxHeartbeats_3246_);
lean_ctor_set(v___x_3256_, 10, v_quotContext_3247_);
lean_ctor_set(v___x_3256_, 11, v_currMacroScope_3248_);
lean_ctor_set(v___x_3256_, 12, v_cancelTk_x3f_3250_);
lean_ctor_set(v___x_3256_, 13, v_inheritedTraceOptions_3252_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*14, v_diag_3249_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*14 + 1, v_suppressElabErrors_3251_);
v___x_3257_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v___x_3254_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___x_3256_, v___y_2946_);
lean_dec_ref(v___x_3256_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref(v___x_3257_);
lean_inc(v_fst_2960_);
lean_inc(v_fst_2956_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_2956_, v_fst_2960_, v_a_3258_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
v___y_3207_ = v___x_3259_;
goto v___jp_3206_;
}
else
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3257_);
v_a_3203_ = v_a_3260_;
goto v___jp_3202_;
}
}
else
{
lean_object* v_a_3261_; 
lean_dec(v___x_3213_);
v_a_3261_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3236_);
v_a_3203_ = v_a_3261_;
goto v___jp_3202_;
}
}
else
{
lean_dec(v_a_3224_);
lean_dec(v___x_3213_);
v_a_3203_ = v_a_3233_;
goto v___jp_3202_;
}
}
}
}
else
{
lean_object* v_a_3264_; 
lean_dec(v___x_3213_);
v_a_3264_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3223_);
v_a_3203_ = v_a_3264_;
goto v___jp_3202_;
}
}
}
else
{
lean_object* v_a_3265_; 
lean_dec(v___x_3213_);
v_a_3265_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3214_);
v_a_3203_ = v_a_3265_;
goto v___jp_3202_;
}
v___jp_3186_:
{
if (v___y_3188_ == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v___y_3187_);
lean_del_object(v___x_3184_);
v___x_3189_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3182_, v___y_3188_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v___x_3189_);
lean_inc(v_a_2985_);
v___x_3190_ = lean_array_push(v_fst_2960_, v_a_2985_);
v_fst_2980_ = v_fst_2956_;
v_snd_2981_ = v___x_3190_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3191_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3189_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3189_);
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
else
{
lean_object* v___x_3200_; 
lean_dec(v_a_3182_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 1);
lean_ctor_set(v___x_3184_, 0, v___y_3187_);
v___x_3200_ = v___x_3184_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___y_3187_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
v___jp_3202_:
{
uint8_t v___x_3204_; 
v___x_3204_ = l_Lean_Exception_isInterrupt(v_a_3203_);
if (v___x_3204_ == 0)
{
uint8_t v___x_3205_; 
lean_inc_ref(v_a_3203_);
v___x_3205_ = l_Lean_Exception_isRuntime(v_a_3203_);
v___y_3187_ = v_a_3203_;
v___y_3188_ = v___x_3205_;
goto v___jp_3186_;
}
else
{
v___y_3187_ = v_a_3203_;
v___y_3188_ = v___x_3204_;
goto v___jp_3186_;
}
}
v___jp_3206_:
{
if (lean_obj_tag(v___y_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_snd_3209_; lean_object* v_fst_3210_; lean_object* v_snd_3211_; 
lean_del_object(v___x_3184_);
lean_dec(v_a_3182_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3208_ = lean_ctor_get(v___y_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___y_3207_);
v_snd_3209_ = lean_ctor_get(v_a_3208_, 1);
lean_inc(v_snd_3209_);
lean_dec(v_a_3208_);
v_fst_3210_ = lean_ctor_get(v_snd_3209_, 0);
lean_inc(v_fst_3210_);
v_snd_3211_ = lean_ctor_get(v_snd_3209_, 1);
lean_inc(v_snd_3211_);
lean_dec(v_snd_3209_);
v_fst_2980_ = v_fst_3210_;
v_snd_2981_ = v_snd_3211_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v___y_3207_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___y_3207_);
v_a_3203_ = v_a_3212_;
goto v___jp_3202_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_3267_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3181_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3181_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
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
v___jp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v_snd_2967_);
v___x_2969_ = v___x_2963_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_snd_2967_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_snd_2961_);
v___x_2969_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v___x_2969_);
lean_ctor_set(v___x_2958_, 0, v_fst_2966_);
v___x_2971_ = v___x_2958_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_fst_2966_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v_a_2949_ = v___x_2971_;
goto v___jp_2948_;
}
}
}
v___jp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_snd_2976_);
lean_ctor_set(v___x_2977_, 1, v_snd_2961_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_fst_2975_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v_a_2949_ = v___x_2978_;
goto v___jp_2948_;
}
v___jp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_snd_2981_);
lean_ctor_set(v___x_2982_, 1, v_snd_2961_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_fst_2980_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v_a_2949_ = v___x_2983_;
goto v___jp_2948_;
}
v___jp_2986_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_inc(v_a_2985_);
v___x_2987_ = lean_array_push(v_fst_2960_, v_a_2985_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v_snd_2961_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_fst_2956_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v_a_2949_ = v___x_2989_;
goto v___jp_2948_;
}
v___jp_2990_:
{
if (v___y_2993_ == 0)
{
lean_object* v___x_2994_; 
lean_dec_ref(v___y_2991_);
v___x_2994_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_2992_, v___y_2993_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; 
lean_dec_ref(v___x_2994_);
lean_inc(v_a_2985_);
v___x_2995_ = lean_array_push(v_fst_2960_, v_a_2985_);
v_fst_2975_ = v_fst_2956_;
v_snd_2976_ = v___x_2995_;
goto v___jp_2974_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v_a_2996_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2994_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref(v___y_2992_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_dec(v_fst_2956_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___y_2991_);
return v___x_3004_;
}
}
v___jp_3005_:
{
if (v___y_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec_ref(v___y_3006_);
v___x_3009_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_3007_, v___y_3008_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref(v___x_3009_);
lean_inc(v_a_2985_);
v___x_3010_ = lean_array_push(v_fst_2960_, v_a_2985_);
v_fst_2966_ = v_fst_2956_;
v_snd_2967_ = v___x_3010_;
goto v___jp_2965_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v_a_3011_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v___x_3019_; 
lean_dec_ref(v___y_3007_);
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
v___x_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___y_3006_);
return v___x_3019_;
}
}
}
}
}
v___jp_2948_:
{
size_t v___x_2950_; size_t v___x_2951_; 
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_add(v_i_2937_, v___x_2950_);
v_i_2937_ = v___x_2951_;
v_b_2938_ = v_a_2949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___boxed(lean_object* v_as_3277_, lean_object* v_sz_3278_, lean_object* v_i_3279_, lean_object* v_b_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
size_t v_sz_boxed_3290_; size_t v_i_boxed_3291_; lean_object* v_res_3292_; 
v_sz_boxed_3290_ = lean_unbox_usize(v_sz_3278_);
lean_dec(v_sz_3278_);
v_i_boxed_3291_ = lean_unbox_usize(v_i_3279_);
lean_dec(v_i_3279_);
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v_as_3277_, v_sz_boxed_3290_, v_i_boxed_3291_, v_b_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v_as_3277_);
return v_res_3292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13));
v___x_3329_ = l_String_toRawSubstring_x27(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19));
v___x_3341_ = l_String_toRawSubstring_x27(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22(void){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Array_mkArray0(lean_box(0));
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext(lean_object* v_optConfig_3349_, lean_object* v_lemmas_3350_, uint8_t v_ignoreStarArg_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_3349_, v_a_3352_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3359_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; uint8_t v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; size_t v_sz_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = 0;
v___x_3366_ = lean_unsigned_to_nat(1u);
v___x_3367_ = l_Lean_Syntax_getArg(v_lemmas_3350_, v___x_3366_);
v___x_3368_ = l_Lean_Syntax_getSepArgs(v___x_3367_);
lean_dec(v___x_3367_);
v___x_3369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1));
v___x_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3370_, 0, v_a_3364_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v_sz_3371_ = lean_array_size(v___x_3368_);
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v___x_3368_, v_sz_3371_, v___x_3372_, v___x_3370_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec_ref(v___x_3368_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v_snd_3375_; lean_object* v_fst_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3483_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3373_);
v_snd_3375_ = lean_ctor_get(v_a_3374_, 1);
v_fst_3376_ = lean_ctor_get(v_a_3374_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_a_3374_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3378_ = v_a_3374_;
v_isShared_3379_ = v_isSharedCheck_3483_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_snd_3375_);
lean_inc(v_fst_3376_);
lean_dec(v_a_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3483_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3482_; 
v_fst_3380_ = lean_ctor_get(v_snd_3375_, 0);
v_snd_3381_ = lean_ctor_get(v_snd_3375_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_snd_3375_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3383_ = v_snd_3375_;
v_isShared_3384_ = v_isSharedCheck_3482_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_snd_3381_);
lean_inc(v_fst_3380_);
lean_dec(v_snd_3375_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3482_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_ref_3385_; lean_object* v_quotContext_3386_; lean_object* v_currMacroScope_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v_ref_3385_ = lean_ctor_get(v_a_3358_, 5);
v_quotContext_3386_ = lean_ctor_get(v_a_3358_, 10);
v_currMacroScope_3387_ = lean_ctor_get(v_a_3358_, 11);
v___x_3388_ = l_Lean_SourceInfo_fromRef(v_ref_3385_, v___x_3365_);
v___x_3389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2));
v___x_3390_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3));
lean_inc(v___x_3388_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 2);
lean_ctor_set(v___x_3383_, 1, v___x_3389_);
lean_ctor_set(v___x_3383_, 0, v___x_3388_);
v___x_3392_ = v___x_3383_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3389_);
v___x_3392_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5));
v___x_3394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7));
v___x_3395_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9));
v___x_3396_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11));
v___x_3397_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12));
lean_inc(v___x_3388_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 2);
lean_ctor_set(v___x_3378_, 1, v___x_3397_);
lean_ctor_set(v___x_3378_, 0, v___x_3388_);
v___x_3399_ = v___x_3378_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3400_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14);
v___x_3401_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15));
lean_inc_n(v_currMacroScope_3387_, 2);
lean_inc_n(v_quotContext_3386_, 2);
v___x_3402_ = l_Lean_addMacroScope(v_quotContext_3386_, v___x_3401_, v_currMacroScope_3387_);
v___x_3403_ = lean_box(0);
lean_inc_n(v___x_3388_, 14);
v___x_3404_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3388_);
lean_ctor_set(v___x_3404_, 1, v___x_3400_);
lean_ctor_set(v___x_3404_, 2, v___x_3402_);
lean_ctor_set(v___x_3404_, 3, v___x_3403_);
v___x_3405_ = l_Lean_Syntax_node2(v___x_3388_, v___x_3396_, v___x_3399_, v___x_3404_);
v___x_3406_ = l_Lean_Syntax_node1(v___x_3388_, v___x_3395_, v___x_3405_);
v___x_3407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17));
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18));
v___x_3409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3388_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20);
v___x_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21));
v___x_3412_ = l_Lean_addMacroScope(v_quotContext_3386_, v___x_3411_, v_currMacroScope_3387_);
v___x_3413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3388_);
lean_ctor_set(v___x_3413_, 1, v___x_3410_);
lean_ctor_set(v___x_3413_, 2, v___x_3412_);
lean_ctor_set(v___x_3413_, 3, v___x_3403_);
v___x_3414_ = l_Lean_Syntax_node2(v___x_3388_, v___x_3407_, v___x_3409_, v___x_3413_);
v___x_3415_ = l_Lean_Syntax_node1(v___x_3388_, v___x_3395_, v___x_3414_);
v___x_3416_ = l_Lean_Syntax_node2(v___x_3388_, v___x_3394_, v___x_3406_, v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node1(v___x_3388_, v___x_3393_, v___x_3416_);
v___x_3418_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22);
v___x_3419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3388_);
lean_ctor_set(v___x_3419_, 1, v___x_3394_);
lean_ctor_set(v___x_3419_, 2, v___x_3418_);
v___x_3420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23));
v___x_3421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3388_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24));
v___x_3423_ = l_Lean_Syntax_SepArray_ofElems(v___x_3422_, v_fst_3380_);
lean_dec(v_fst_3380_);
v___x_3424_ = l_Array_append___redArg(v___x_3418_, v___x_3423_);
lean_dec_ref(v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3388_);
lean_ctor_set(v___x_3425_, 1, v___x_3394_);
lean_ctor_set(v___x_3425_, 2, v___x_3424_);
v___x_3426_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25));
v___x_3427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3388_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_Syntax_node3(v___x_3388_, v___x_3394_, v___x_3421_, v___x_3425_, v___x_3427_);
lean_inc_ref_n(v___x_3419_, 2);
v___x_3429_ = l_Lean_Syntax_node6(v___x_3388_, v___x_3390_, v___x_3392_, v___x_3417_, v___x_3419_, v___x_3419_, v___x_3428_, v___x_3419_);
v___x_3430_ = 0;
v___x_3431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26));
v___x_3432_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_3429_, v___x_3365_, v___x_3430_, v_ignoreStarArg_3351_, v___x_3431_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v___x_3429_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3471_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_specThms_3438_; lean_object* v___y_3439_; uint8_t v___x_3449_; 
v___x_3449_ = lean_unbox(v_snd_3381_);
lean_dec(v_snd_3381_);
if (v___x_3449_ == 0)
{
v_specThms_3438_ = v_fst_3376_;
v___y_3439_ = v_a_3356_;
goto v___jp_3437_;
}
else
{
if (v_ignoreStarArg_3351_ == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Meta_getPropHyps(v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; size_t v_sz_3452_; lean_object* v___x_3453_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref(v___x_3450_);
v_sz_3452_ = lean_array_size(v_a_3451_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_a_3451_, v_sz_3452_, v___x_3372_, v_fst_3376_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3451_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v_specThms_3438_ = v_a_3454_;
v___y_3439_ = v_a_3356_;
goto v___jp_3437_;
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3435_);
lean_dec(v_a_3433_);
lean_dec(v_a_3362_);
v_a_3455_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3453_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3453_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_del_object(v___x_3435_);
lean_dec(v_a_3433_);
lean_dec(v_fst_3376_);
lean_dec(v_a_3362_);
v_a_3463_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3450_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3450_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
v_specThms_3438_ = v_fst_3376_;
v___y_3439_ = v_a_3356_;
goto v___jp_3437_;
}
}
v___jp_3437_:
{
lean_object* v_lctx_3440_; lean_object* v_ctx_3441_; lean_object* v_simprocs_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v_lctx_3440_ = lean_ctor_get(v___y_3439_, 2);
v_ctx_3441_ = lean_ctor_get(v_a_3433_, 0);
lean_inc_ref(v_ctx_3441_);
v_simprocs_3442_ = lean_ctor_get(v_a_3433_, 1);
lean_inc_ref(v_simprocs_3442_);
lean_dec(v_a_3433_);
v___x_3443_ = lean_box(1);
lean_inc_ref(v_lctx_3440_);
v___x_3444_ = lean_local_ctx_num_indices(v_lctx_3440_);
v___x_3445_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3445_, 0, v_a_3362_);
lean_ctor_set(v___x_3445_, 1, v_specThms_3438_);
lean_ctor_set(v___x_3445_, 2, v_ctx_3441_);
lean_ctor_set(v___x_3445_, 3, v_simprocs_3442_);
lean_ctor_set(v___x_3445_, 4, v___x_3443_);
lean_ctor_set(v___x_3445_, 5, v___x_3444_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3445_);
v___x_3447_ = v___x_3435_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_snd_3381_);
lean_dec(v_fst_3376_);
lean_dec(v_a_3362_);
v_a_3472_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3432_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3432_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
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
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v_a_3362_);
v_a_3484_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3373_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3373_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v_a_3362_);
v_a_3492_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3363_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3363_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3500_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3361_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3361_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___boxed(lean_object* v_optConfig_3508_, lean_object* v_lemmas_3509_, lean_object* v_ignoreStarArg_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
uint8_t v_ignoreStarArg_boxed_3520_; lean_object* v_res_3521_; 
v_ignoreStarArg_boxed_3520_ = lean_unbox(v_ignoreStarArg_3510_);
v_res_3521_ = l_Lean_Elab_Tactic_Do_mkSpecContext(v_optConfig_3508_, v_lemmas_3509_, v_ignoreStarArg_boxed_3520_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_lemmas_3509_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_object* v_00_u03b1_3522_, lean_object* v_msg_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3523_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_msg_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(v_00_u03b1_3534_, v_msg_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_object* v_00_u03b1_3546_, lean_object* v_constName_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___boxed(lean_object* v_00_u03b1_3558_, lean_object* v_constName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(v_00_u03b1_3558_, v_constName_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(lean_object* v_as_3570_, size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_3570_, v_sz_3571_, v_i_3572_, v_b_3573_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___boxed(lean_object* v_as_3584_, lean_object* v_sz_3585_, lean_object* v_i_3586_, lean_object* v_b_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
size_t v_sz_boxed_3597_; size_t v_i_boxed_3598_; lean_object* v_res_3599_; 
v_sz_boxed_3597_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v_i_boxed_3598_ = lean_unbox_usize(v_i_3586_);
lean_dec(v_i_3586_);
v_res_3599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(v_as_3584_, v_sz_boxed_3597_, v_i_boxed_3598_, v_b_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v_as_3584_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_object* v_00_u03b1_3600_, lean_object* v_ref_3601_, lean_object* v_constName_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3601_, v_constName_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_ref_3614_, lean_object* v_constName_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(v_00_u03b1_3613_, v_ref_3614_, v_constName_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v_ref_3614_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3626_, lean_object* v_ref_3627_, lean_object* v_msg_3628_, lean_object* v_declHint_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3627_, v_msg_3628_, v_declHint_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3640_, lean_object* v_ref_3641_, lean_object* v_msg_3642_, lean_object* v_declHint_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(v_00_u03b1_3640_, v_ref_3641_, v_msg_3642_, v_declHint_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v_ref_3641_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_3654_, lean_object* v_declHint_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3654_, v_declHint_3655_, v___y_3663_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_3666_, lean_object* v_declHint_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_3666_, v_declHint_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_object* v_00_u03b1_3678_, lean_object* v_ref_3679_, lean_object* v_msg_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3679_, v_msg_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b1_3691_, lean_object* v_ref_3692_, lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(v_00_u03b1_3691_, v_ref_3692_, v_msg_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v_ref_3692_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object* v___x_3704_, lean_object* v___x_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_3704_, v___x_3705_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object* v___x_3715_, lean_object* v___x_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(v___x_3715_, v___x_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_inheritedTraceOptions_3734_; lean_object* v___x_3735_; 
v_inheritedTraceOptions_3734_ = lean_ctor_get(v___y_3731_, 13);
lean_inc_ref(v_inheritedTraceOptions_3734_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_inheritedTraceOptions_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_options_3753_; lean_object* v___x_3754_; 
v_options_3753_ = lean_ctor_get(v___y_3750_, 2);
lean_inc_ref(v_options_3753_);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_options_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
return v_res_3763_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3766_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_3769_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3768_, v___x_3767_, v___x_3766_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v___f_3774_; lean_object* v___x_3775_; 
v___x_3772_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4);
v___f_3773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_3774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_3775_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3774_, v___f_3773_, v___x_3772_);
return v___x_3775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3776_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5);
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_3778_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_3779_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3778_, v___x_3777_, v___x_3776_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; 
v___x_3780_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6);
v___f_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_3782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_3783_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3782_, v___f_3781_, v___x_3780_);
return v___x_3783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_instMonadEIO(lean_box(0));
return v___x_3784_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8);
v___x_3786_ = l_StateRefT_x27_instMonad___redArg(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_3794_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3793_, v___x_3792_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15);
v___f_3796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_3797_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16);
v___x_3799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_3800_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3799_, v___x_3798_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17);
v___f_3802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_3803_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3802_, v___x_3801_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___f_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18);
v___f_3805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_3806_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3805_, v___x_3804_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19);
v___f_3808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___x_3809_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3808_, v___x_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_3812_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__15));
v___x_3813_ = l_Lean_Name_append(v___x_3812_, v___x_3811_);
return v___x_3813_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___f_3816_; 
v___x_3814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_3815_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_3816_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3816_, 0, v___x_3815_);
lean_closure_set(v___f_3816_, 1, v___x_3814_);
return v___f_3816_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24(void){
_start:
{
lean_object* v___f_3817_; lean_object* v___f_3818_; lean_object* v___f_3819_; 
v___f_3817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_3818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23);
v___f_3819_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3819_, 0, v___f_3818_);
lean_closure_set(v___f_3819_, 1, v___f_3817_);
return v___f_3819_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25(void){
_start:
{
lean_object* v___f_3820_; lean_object* v___f_3821_; lean_object* v___f_3822_; 
v___f_3820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_3821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3822_, 0, v___f_3821_);
lean_closure_set(v___f_3822_, 1, v___f_3820_);
return v___f_3822_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26(void){
_start:
{
lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___f_3825_; 
v___f_3823_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___f_3824_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25);
v___f_3825_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3825_, 0, v___f_3824_);
lean_closure_set(v___f_3825_, 1, v___f_3823_);
return v___f_3825_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27));
v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
return v___x_3828_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33));
v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(lean_object* v_xs_3838_, lean_object* v_k_3839_, lean_object* v_runInBase_3840_, lean_object* v_i_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3857_; lean_object* v_a_3858_; lean_object* v_a_3862_; lean_object* v___y_3865_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3867_ = lean_array_get_size(v_xs_3838_);
v___x_3868_ = lean_nat_dec_lt(v_i_3841_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec(v_i_3841_);
lean_inc(v_a_3847_);
lean_inc_ref(v_a_3846_);
lean_inc(v_a_3845_);
lean_inc_ref(v_a_3844_);
lean_inc(v_a_3843_);
lean_inc_ref(v_a_3842_);
v___x_3869_ = lean_apply_9(v_runInBase_3840_, lean_box(0), v_k_3839_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, lean_box(0));
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v_toMonadRef_3871_; lean_object* v___x_3872_; lean_object* v_toApplicative_3873_; lean_object* v_toFunctor_3874_; lean_object* v_toSeq_3875_; lean_object* v_toSeqLeft_3876_; lean_object* v_toSeqRight_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___f_3881_; lean_object* v___x_3882_; lean_object* v___f_3883_; lean_object* v___f_3884_; lean_object* v___f_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v_toApplicative_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3984_; 
v___x_3870_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7);
v_toMonadRef_3871_ = lean_ctor_get(v___x_3870_, 0);
v___x_3872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9);
v_toApplicative_3873_ = lean_ctor_get(v___x_3872_, 0);
v_toFunctor_3874_ = lean_ctor_get(v_toApplicative_3873_, 0);
v_toSeq_3875_ = lean_ctor_get(v_toApplicative_3873_, 2);
v_toSeqLeft_3876_ = lean_ctor_get(v_toApplicative_3873_, 3);
v_toSeqRight_3877_ = lean_ctor_get(v_toApplicative_3873_, 4);
v___f_3878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10));
v___f_3879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11));
lean_inc_ref_n(v_toFunctor_3874_, 2);
v___f_3880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3880_, 0, v_toFunctor_3874_);
v___f_3881_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3881_, 0, v_toFunctor_3874_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___f_3880_);
lean_ctor_set(v___x_3882_, 1, v___f_3881_);
lean_inc(v_toSeqRight_3877_);
v___f_3883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3883_, 0, v_toSeqRight_3877_);
lean_inc(v_toSeqLeft_3876_);
v___f_3884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3884_, 0, v_toSeqLeft_3876_);
lean_inc(v_toSeq_3875_);
v___f_3885_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3885_, 0, v_toSeq_3875_);
v___x_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3882_);
lean_ctor_set(v___x_3886_, 1, v___f_3878_);
lean_ctor_set(v___x_3886_, 2, v___f_3885_);
lean_ctor_set(v___x_3886_, 3, v___f_3884_);
lean_ctor_set(v___x_3886_, 4, v___f_3883_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___f_3879_);
v___x_3888_ = l_StateRefT_x27_instMonad___redArg(v___x_3887_);
v_toApplicative_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v___x_3888_, 1);
lean_dec(v_unused_3985_);
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3984_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_toApplicative_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3984_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v_toFunctor_3893_; lean_object* v_toSeq_3894_; lean_object* v_toSeqLeft_3895_; lean_object* v_toSeqRight_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3982_; 
v_toFunctor_3893_ = lean_ctor_get(v_toApplicative_3889_, 0);
v_toSeq_3894_ = lean_ctor_get(v_toApplicative_3889_, 2);
v_toSeqLeft_3895_ = lean_ctor_get(v_toApplicative_3889_, 3);
v_toSeqRight_3896_ = lean_ctor_get(v_toApplicative_3889_, 4);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_toApplicative_3889_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v_toApplicative_3889_, 1);
lean_dec(v_unused_3983_);
v___x_3898_ = v_toApplicative_3889_;
v_isShared_3899_ = v_isSharedCheck_3982_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_toSeqRight_3896_);
lean_inc(v_toSeqLeft_3895_);
lean_inc(v_toSeq_3894_);
lean_inc(v_toFunctor_3893_);
lean_dec(v_toApplicative_3889_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3982_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_x_3900_; lean_object* v___f_3901_; lean_object* v___f_3902_; lean_object* v___f_3903_; lean_object* v___f_3904_; lean_object* v___x_3905_; lean_object* v___f_3906_; lean_object* v___f_3907_; lean_object* v___f_3908_; lean_object* v___x_3910_; 
v_x_3900_ = lean_array_fget_borrowed(v_xs_3838_, v_i_3841_);
v___f_3901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12));
v___f_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13));
lean_inc_ref(v_toFunctor_3893_);
v___f_3903_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3903_, 0, v_toFunctor_3893_);
v___f_3904_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3904_, 0, v_toFunctor_3893_);
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___f_3903_);
lean_ctor_set(v___x_3905_, 1, v___f_3904_);
v___f_3906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3906_, 0, v_toSeqRight_3896_);
v___f_3907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3907_, 0, v_toSeqLeft_3895_);
v___f_3908_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3908_, 0, v_toSeq_3894_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 4, v___f_3906_);
lean_ctor_set(v___x_3898_, 3, v___f_3907_);
lean_ctor_set(v___x_3898_, 2, v___f_3908_);
lean_ctor_set(v___x_3898_, 1, v___f_3901_);
lean_ctor_set(v___x_3898_, 0, v___x_3905_);
v___x_3910_ = v___x_3898_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___f_3901_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v___f_3908_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v___f_3907_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v___f_3906_);
v___x_3910_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3912_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v___f_3902_);
lean_ctor_set(v___x_3891_, 0, v___x_3910_);
v___x_3912_ = v___x_3891_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v___f_3902_);
v___x_3912_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v___x_3913_ = l_StateRefT_x27_instMonad___redArg(v___x_3912_);
v___x_3914_ = l_ReaderT_instMonad___redArg(v___x_3913_);
v___x_3915_ = l_Lean_Expr_fvarId_x21(v_x_3900_);
v___x_3916_ = lean_unsigned_to_nat(100u);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3917_, 0, v___x_3915_);
lean_closure_set(v___f_3917_, 1, v___x_3916_);
v___x_3918_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_3917_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___f_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref(v___x_3918_);
v___f_3920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14));
v___x_3921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20);
v___x_3922_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_3920_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___f_3924_; lean_object* v___x_3925_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref(v___x_3922_);
v___f_3924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21));
v___x_3925_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_3924_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; uint8_t v_hasTrace_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v_hasTrace_3927_ = lean_ctor_get_uint8(v_a_3926_, sizeof(void*)*1);
if (v_hasTrace_3927_ == 0)
{
lean_dec(v_a_3926_);
lean_dec(v_a_3923_);
lean_dec_ref(v___x_3914_);
goto v___jp_3928_;
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; 
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_3932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22);
v___x_3933_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_a_3923_, v_a_3926_, v___x_3932_);
lean_dec(v_a_3926_);
lean_dec(v_a_3923_);
if (v___x_3933_ == 0)
{
lean_dec_ref(v___x_3914_);
goto v___jp_3928_;
}
else
{
lean_object* v_proof_3934_; lean_object* v___f_3935_; lean_object* v___x_3936_; lean_object* v___y_3938_; 
v_proof_3934_ = lean_ctor_get(v_a_3919_, 2);
v___f_3935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26);
v___x_3936_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28);
switch(lean_obj_tag(v_proof_3934_))
{
case 0:
{
lean_object* v_declName_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_declName_3952_ = lean_ctor_get(v_proof_3934_, 0);
v___x_3953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30);
lean_inc(v_declName_3952_);
v___x_3954_ = l_Lean_MessageData_ofName(v_declName_3952_);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___y_3938_ = v___x_3955_;
goto v___jp_3937_;
}
case 1:
{
lean_object* v_fvarId_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_fvarId_3956_ = lean_ctor_get(v_proof_3934_, 0);
v___x_3957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32);
lean_inc(v_fvarId_3956_);
v___x_3958_ = l_Lean_mkFVar(v_fvarId_3956_);
v___x_3959_ = l_Lean_MessageData_ofExpr(v___x_3958_);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3957_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___y_3938_ = v___x_3960_;
goto v___jp_3937_;
}
default: 
{
lean_object* v_ref_3961_; lean_object* v_proof_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_ref_3961_ = lean_ctor_get(v_proof_3934_, 1);
v_proof_3962_ = lean_ctor_get(v_proof_3934_, 2);
v___x_3963_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34);
lean_inc(v_ref_3961_);
v___x_3964_ = l_Lean_MessageData_ofSyntax(v_ref_3961_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_Do_elabConfig_spec__0_spec__0___closed__20);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
lean_inc_ref(v_proof_3962_);
v___x_3968_ = l_Lean_MessageData_ofExpr(v_proof_3962_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___y_3938_ = v___x_3969_;
goto v___jp_3937_;
}
}
v___jp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_5979__overap_3940_; lean_object* v___x_3941_; 
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3936_);
lean_ctor_set(v___x_3939_, 1, v___y_3938_);
lean_inc_ref(v_toMonadRef_3871_);
v___x_5979__overap_3940_ = l_Lean_addTrace___redArg(v___x_3914_, v___x_3921_, v_toMonadRef_3871_, v___f_3935_, v___x_3931_, v___x_3939_);
lean_inc(v_a_3847_);
lean_inc_ref(v_a_3846_);
lean_inc(v_a_3845_);
lean_inc_ref(v_a_3844_);
lean_inc(v_a_3843_);
lean_inc_ref(v_a_3842_);
v___x_3941_ = lean_apply_7(v___x_5979__overap_3940_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, lean_box(0));
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
lean_inc_ref(v_runInBase_3840_);
lean_inc(v_k_3839_);
v___x_3943_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_3841_, v_a_3919_, v_xs_3838_, v_k_3839_, v_runInBase_3840_, v_a_3942_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
v___y_3865_ = v___x_3943_;
goto v___jp_3864_;
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec(v_a_3919_);
v_a_3944_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3941_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3941_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
lean_inc(v_a_3944_);
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
v___y_3857_ = v___x_3949_;
v_a_3858_ = v_a_3944_;
goto v___jp_3856_;
}
}
}
}
}
}
v___jp_3928_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
lean_inc_ref(v_runInBase_3840_);
lean_inc(v_k_3839_);
v___x_3930_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_3841_, v_a_3919_, v_xs_3838_, v_k_3839_, v_runInBase_3840_, v___x_3929_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
v___y_3865_ = v___x_3930_;
goto v___jp_3864_;
}
}
else
{
lean_object* v_a_3970_; 
lean_dec(v_a_3923_);
lean_dec(v_a_3919_);
lean_dec_ref(v___x_3914_);
v_a_3970_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3925_);
v_a_3862_ = v_a_3970_;
goto v___jp_3861_;
}
}
else
{
lean_object* v_a_3971_; 
lean_dec(v_a_3919_);
lean_dec_ref(v___x_3914_);
v_a_3971_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3922_);
v_a_3862_ = v_a_3971_;
goto v___jp_3861_;
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v___x_3914_);
v_a_3972_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3918_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3918_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
lean_inc(v_a_3972_);
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
v___y_3857_ = v___x_3977_;
v_a_3858_ = v_a_3972_;
goto v___jp_3856_;
}
}
}
}
}
}
}
}
v___jp_3849_:
{
if (v___y_3852_ == 0)
{
if (lean_obj_tag(v___y_3850_) == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v___y_3850_);
lean_dec_ref(v___y_3851_);
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = lean_nat_add(v_i_3841_, v___x_3853_);
lean_dec(v_i_3841_);
v_i_3841_ = v___x_3854_;
goto _start;
}
else
{
lean_dec_ref(v___y_3850_);
lean_dec(v_i_3841_);
lean_dec_ref(v_runInBase_3840_);
lean_dec(v_k_3839_);
return v___y_3851_;
}
}
else
{
lean_dec_ref(v___y_3850_);
lean_dec(v_i_3841_);
lean_dec_ref(v_runInBase_3840_);
lean_dec(v_k_3839_);
return v___y_3851_;
}
}
v___jp_3856_:
{
uint8_t v___x_3859_; 
v___x_3859_ = l_Lean_Exception_isInterrupt(v_a_3858_);
if (v___x_3859_ == 0)
{
uint8_t v___x_3860_; 
lean_inc_ref(v_a_3858_);
v___x_3860_ = l_Lean_Exception_isRuntime(v_a_3858_);
v___y_3850_ = v_a_3858_;
v___y_3851_ = v___y_3857_;
v___y_3852_ = v___x_3860_;
goto v___jp_3849_;
}
else
{
v___y_3850_ = v_a_3858_;
v___y_3851_ = v___y_3857_;
v___y_3852_ = v___x_3859_;
goto v___jp_3849_;
}
}
v___jp_3861_:
{
lean_object* v___x_3863_; 
lean_inc_ref(v_a_3862_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_a_3862_);
v___y_3857_ = v___x_3863_;
v_a_3858_ = v_a_3862_;
goto v___jp_3856_;
}
v___jp_3864_:
{
if (lean_obj_tag(v___y_3865_) == 0)
{
lean_dec(v_i_3841_);
lean_dec_ref(v_runInBase_3840_);
lean_dec(v_k_3839_);
return v___y_3865_;
}
else
{
lean_object* v_a_3866_; 
v_a_3866_ = lean_ctor_get(v___y_3865_, 0);
lean_inc(v_a_3866_);
v___y_3857_ = v___y_3865_;
v_a_3858_ = v_a_3866_;
goto v___jp_3856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(lean_object* v_i_3986_, lean_object* v_a_3987_, lean_object* v_xs_3988_, lean_object* v_k_3989_, lean_object* v_runInBase_3990_, lean_object* v_____r_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_config_3999_; lean_object* v_specThms_4000_; lean_object* v_simpCtx_4001_; lean_object* v_simprocs_4002_; lean_object* v_jps_4003_; lean_object* v_initialCtxSize_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v_config_3999_ = lean_ctor_get(v___y_3992_, 0);
v_specThms_4000_ = lean_ctor_get(v___y_3992_, 1);
v_simpCtx_4001_ = lean_ctor_get(v___y_3992_, 2);
v_simprocs_4002_ = lean_ctor_get(v___y_3992_, 3);
v_jps_4003_ = lean_ctor_get(v___y_3992_, 4);
v_initialCtxSize_4004_ = lean_ctor_get(v___y_3992_, 5);
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = lean_nat_add(v_i_3986_, v___x_4005_);
lean_inc_ref(v_specThms_4000_);
v___x_4007_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_specThms_4000_, v_a_3987_);
lean_inc(v_initialCtxSize_4004_);
lean_inc(v_jps_4003_);
lean_inc_ref(v_simprocs_4002_);
lean_inc_ref(v_simpCtx_4001_);
lean_inc_ref(v_config_3999_);
v___x_4008_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4008_, 0, v_config_3999_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
lean_ctor_set(v___x_4008_, 2, v_simpCtx_4001_);
lean_ctor_set(v___x_4008_, 3, v_simprocs_4002_);
lean_ctor_set(v___x_4008_, 4, v_jps_4003_);
lean_ctor_set(v___x_4008_, 5, v_initialCtxSize_4004_);
v___x_4009_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_3988_, v_k_3989_, v_runInBase_3990_, v___x_4006_, v___x_4008_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec_ref(v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3___boxed(lean_object* v_i_4010_, lean_object* v_a_4011_, lean_object* v_xs_4012_, lean_object* v_k_4013_, lean_object* v_runInBase_4014_, lean_object* v_____r_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4010_, v_a_4011_, v_xs_4012_, v_k_4013_, v_runInBase_4014_, v_____r_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_xs_4012_);
lean_dec(v_i_4010_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___boxed(lean_object* v_xs_4024_, lean_object* v_k_4025_, lean_object* v_runInBase_4026_, lean_object* v_i_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4024_, v_k_4025_, v_runInBase_4026_, v_i_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_xs_4024_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_object* v_m_4036_, lean_object* v_00_u03b1_4037_, lean_object* v_inst_4038_, lean_object* v_xs_4039_, lean_object* v_k_4040_, lean_object* v_runInBase_4041_, lean_object* v_i_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4039_, v_k_4040_, v_runInBase_4041_, v_i_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___boxed(lean_object* v_m_4051_, lean_object* v_00_u03b1_4052_, lean_object* v_inst_4053_, lean_object* v_xs_4054_, lean_object* v_k_4055_, lean_object* v_runInBase_4056_, lean_object* v_i_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(v_m_4051_, v_00_u03b1_4052_, v_inst_4053_, v_xs_4054_, v_k_4055_, v_runInBase_4056_, v_i_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec_ref(v_xs_4054_);
lean_dec_ref(v_inst_4053_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter___redArg(lean_object* v_ex_4066_, lean_object* v_h__1_4067_, lean_object* v_h__2_4068_){
_start:
{
if (lean_obj_tag(v_ex_4066_) == 0)
{
lean_object* v_ref_4069_; lean_object* v_msg_4070_; lean_object* v___x_4071_; 
lean_dec(v_h__1_4067_);
v_ref_4069_ = lean_ctor_get(v_ex_4066_, 0);
lean_inc(v_ref_4069_);
v_msg_4070_ = lean_ctor_get(v_ex_4066_, 1);
lean_inc_ref(v_msg_4070_);
lean_dec_ref(v_ex_4066_);
v___x_4071_ = lean_apply_2(v_h__2_4068_, v_ref_4069_, v_msg_4070_);
return v___x_4071_;
}
else
{
lean_object* v_id_4072_; lean_object* v_extra_4073_; lean_object* v___x_4074_; 
lean_dec(v_h__2_4068_);
v_id_4072_ = lean_ctor_get(v_ex_4066_, 0);
lean_inc(v_id_4072_);
v_extra_4073_ = lean_ctor_get(v_ex_4066_, 1);
lean_inc(v_extra_4073_);
lean_dec_ref(v_ex_4066_);
v___x_4074_ = lean_apply_2(v_h__1_4067_, v_id_4072_, v_extra_4073_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter(lean_object* v_motive_4075_, lean_object* v_ex_4076_, lean_object* v_h__1_4077_, lean_object* v_h__2_4078_){
_start:
{
if (lean_obj_tag(v_ex_4076_) == 0)
{
lean_object* v_ref_4079_; lean_object* v_msg_4080_; lean_object* v___x_4081_; 
lean_dec(v_h__1_4077_);
v_ref_4079_ = lean_ctor_get(v_ex_4076_, 0);
lean_inc(v_ref_4079_);
v_msg_4080_ = lean_ctor_get(v_ex_4076_, 1);
lean_inc_ref(v_msg_4080_);
lean_dec_ref(v_ex_4076_);
v___x_4081_ = lean_apply_2(v_h__2_4078_, v_ref_4079_, v_msg_4080_);
return v___x_4081_;
}
else
{
lean_object* v_id_4082_; lean_object* v_extra_4083_; lean_object* v___x_4084_; 
lean_dec(v_h__2_4078_);
v_id_4082_ = lean_ctor_get(v_ex_4076_, 0);
lean_inc(v_id_4082_);
v_extra_4083_ = lean_ctor_get(v_ex_4076_, 1);
lean_inc(v_extra_4083_);
lean_dec_ref(v_ex_4076_);
v___x_4084_ = lean_apply_2(v_h__1_4077_, v_id_4082_, v_extra_4083_);
return v___x_4084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(lean_object* v_xs_4085_, lean_object* v_k_4086_, lean_object* v_runInBase_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = lean_unsigned_to_nat(0u);
v___x_4096_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4085_, v_k_4086_, v_runInBase_4087_, v___x_4095_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed(lean_object* v_xs_4097_, lean_object* v_k_4098_, lean_object* v_runInBase_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(v_xs_4097_, v_k_4098_, v_runInBase_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec_ref(v_xs_4097_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(lean_object* v_inst_4108_, lean_object* v_inst_4109_, lean_object* v_xs_4110_, lean_object* v_k_4111_){
_start:
{
lean_object* v_toBind_4112_; lean_object* v_liftWith_4113_; lean_object* v_restoreM_4114_; lean_object* v___f_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_toBind_4112_ = lean_ctor_get(v_inst_4108_, 1);
lean_inc(v_toBind_4112_);
lean_dec_ref(v_inst_4108_);
v_liftWith_4113_ = lean_ctor_get(v_inst_4109_, 0);
lean_inc(v_liftWith_4113_);
v_restoreM_4114_ = lean_ctor_get(v_inst_4109_, 1);
lean_inc(v_restoreM_4114_);
lean_dec_ref(v_inst_4109_);
v___f_4115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4115_, 0, v_xs_4110_);
lean_closure_set(v___f_4115_, 1, v_k_4111_);
v___x_4116_ = lean_apply_2(v_liftWith_4113_, lean_box(0), v___f_4115_);
v___x_4117_ = lean_apply_1(v_restoreM_4114_, lean_box(0));
v___x_4118_ = lean_apply_4(v_toBind_4112_, lean_box(0), lean_box(0), v___x_4116_, v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs(lean_object* v_m_4119_, lean_object* v_00_u03b1_4120_, lean_object* v_inst_4121_, lean_object* v_inst_4122_, lean_object* v_xs_4123_, lean_object* v_k_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(v_inst_4121_, v_inst_4122_, v_xs_4123_, v_k_4124_);
return v___x_4125_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_mvcgen_warning = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_mvcgen_warning);
lean_dec_ref(res);
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
